package eu.kanade.tachiyomi.animeextension.en.miruro

import android.util.Base64
import android.util.Log
import aniyomi.lib.cloudflareinterceptor.CloudflareInterceptor
import aniyomi.lib.m3u8server.M3u8Integration
import aniyomi.lib.megacloudextractor.MegaCloudExtractor
import aniyomi.lib.omniembedextractor.OmniEmbedExtractor
import aniyomi.lib.rapidcloudextractor.RapidCloudExtractor
import eu.kanade.tachiyomi.animesource.model.Track
import eu.kanade.tachiyomi.animesource.model.Video
import okhttp3.Headers
import okhttp3.HttpUrl.Companion.toHttpUrlOrNull
import okhttp3.OkHttpClient
import okhttp3.Protocol
import okhttp3.Request
import okhttp3.Response
import java.util.concurrent.TimeUnit
import java.util.zip.GZIPInputStream

class MiruroExtractor(
    private val client: OkHttpClient,
    private val pipeKey: ByteArray,
    private val proxyKey: ByteArray,
    private val headers: Headers,
    private val preferences: android.content.SharedPreferences,
    private val mirrorBaseUrl: String,
    private val resolveDisplayName: (String) -> String,
) {

    private fun decompressPayload(rawBytes: ByteArray, contentEncoding: String): ByteArray {
        if (rawBytes.isEmpty()) return rawBytes
        val isGzip = contentEncoding.equals("gzip", true) ||
            (rawBytes.size >= 2 && rawBytes[0] == 0x1F.toByte() && rawBytes[1] == 0x8B.toByte())
        if (isGzip) {
            return runCatching {
                GZIPInputStream(java.io.ByteArrayInputStream(rawBytes)).use { it.readBytes() }
            }.getOrDefault(rawBytes)
        }
        val isBrotli = contentEncoding.equals("br", true) ||
            (rawBytes.isNotEmpty() && rawBytes[0] == 0x1B.toByte())
        if (isBrotli) {
            val decompressed = runCatching {
                val clazz = Class.forName("org.brotli.dec.BrotliInputStream")
                val stream = clazz.getConstructor(java.io.InputStream::class.java)
                    .newInstance(java.io.ByteArrayInputStream(rawBytes)) as java.io.InputStream
                stream.use { it.readBytes() }
            }.getOrNull()
            if (decompressed != null) return decompressed
        }
        return rawBytes
    }

    companion object {
        private const val TAG = "MiruroExtractor"

        private const val PROXY_DELAY_MS = 900L

        /**
         * Host patterns that signal a Zoro-style embed (MegaCloud / RapidCloud
         * / ChillX family). Pre-routed to their dedicated extractors rather
         * than handed to OmniEmbedExtractor, which has no entry for these
         * domains and would silently return an empty list.
         */
        private val MEGACLOUD_HOSTS = listOf("megacloud.tv", "megacloud.club")
        private val RAPID_CLOUD_HOSTS = listOf("rapid-cloud.co", "scloud")

        /**
         * Placeholder for MegaCloud's external decryption endpoint; only used
         * by the encrypted-code path. The vast majority of current streams
         * return `.m3u8` directly (`data.encrypted == false` OR `.m3u8 in
         * encoded`), short-circuiting any key fetch. No prior call site ever
         * instantiated these extractors, so no production value exists to
         * mirror (confirmed by grep).
         */
        private const val MEGACLOUD_API_PLACEHOLDER = "https://megacloud.example/decrypt/"

        /**
         * Referer that StreamDto defaults to in [MiruroDto.StreamDto]. The
         * pipe API populates this as `https://kwik.cx/` for kwik-served HLS
         * streams (AnimePahe) but leaves the kwik default for many other
         * providers, including Miruro's own `vault-*.owocdn.top` CDN. Using
         * the kwik referer to fetch owocdn m3u8 is wrong — that host expects
         * a Miruro referer (the active mirror baseUrl) and 403s otherwise,
         * which previously triggered [CloudflareInterceptor] and the crash
         * chain documented in [MiruroExtractor]'s m3u8 path.
         */
        internal const val KWIK_DEFAULT_REFERER = "https://kwik.cx/"

        /**
         * Miruro frontend proxy servers (from `VITE_PROXY_A` / `VITE_PROXY_B`
         * in `env2.js`). The frontend wraps every provider stream URL through
         * one of these proxies: the proxy fetches the upstream m3u8/segment
         * and relays it back, bypassing CORS and header-gating that would
         * 403 a direct fetch from outside the browser.
         */
        private const val PROXY = "https://s1.watami.win/"

        /**
         * FNV-1a 32-bit hash constants (IETF RFC 7020).
         * Used by the frontend to deterministically select between
         * [PROXY_A] and [PROXY_B] based on episode/anilist IDs.
         */
        private const val FNV_OFFSET_BASIS: Int = 2166136261.toInt()
        private const val FNV_PRIME: Int = 16777619

        /**
         * Encode a [ByteArray] to base64url without padding, matching the
         * frontend's `ix()` / `ax()` obfuscation step (`btoa` + replace
         * `+`→`-`, `/`→`_`, strip `=`).
         */
        private fun base64UrlNoPad(data: ByteArray): String = Base64.encodeToString(data, Base64.NO_WRAP or Base64.URL_SAFE or Base64.NO_PADDING)

        /**
         * XOR-obfuscate a UTF-8 string with [key] bytes (cycled) and
         * base64url-encode the result. Mirrors the frontend's `ix()`
         * function from `WatchRoute-B2vRFobK.js`.
         */
        private fun xorEncode(input: String, key: ByteArray): String {
            val bytes = input.toByteArray(Charsets.UTF_8)
            val out = ByteArray(bytes.size)
            for (i in bytes.indices) {
                out[i] = (bytes[i].toInt() xor key[i % key.size].toInt()).toByte()
            }
            return base64UrlNoPad(out)
        }

        /**
         * FNV-1a 32-bit hash of a string, returning the hash mod 2 to
         * deterministically select between [PROXY_A] (even) and [PROXY_B]
         * (odd). Mirrors the frontend's `Xb()` function.
         *
         * If [seed] is blank, defaults to 0 (→ PROXY_A).
         */
        private fun fnv1aMod2(seed: String): Int {
            if (seed.isEmpty()) return 0
            var hash = FNV_OFFSET_BASIS
            for (b in seed.toByteArray(Charsets.UTF_8)) {
                hash = hash xor (b.toInt() and 0xFF)
                hash *= FNV_PRIME
            }
            return hash and 1
        }

        /**
         * Build a Miruro proxy URL wrapping [streamUrl] and [referer]
         * through `vault01/02.ultracloud.cc`. The proxy fetches the upstream
         * content and relays it, bypassing CORS/403s from direct fetches.
         *
         * URL format (from frontend `cx()` / `lx()`):
         * `{proxyBase}{xorEncode(streamUrl)}~{xorEncode(referer)}/pl.m3u8`
         *
         * If [proxyKey] is empty, returns the original [streamUrl] unchanged
         * (no proxy wrapping possible).
         */
        fun buildProxiedUrl(
            streamUrl: String,
            referer: String,
            proxyKey: ByteArray,
            proxySeed: String,
        ): String {
            if (proxyKey.isEmpty()) {
                Log.w(TAG, "buildProxiedUrl: Proxy key is empty; cannot build Watami URL")
                return ""
            }

            val encodedStream = xorEncode(streamUrl, proxyKey)
            val encodedReferer = xorEncode(referer, proxyKey)
            val result = "${PROXY}$encodedStream~$encodedReferer/pl.m3u8"

            Log.d(TAG, "buildProxiedUrl: streamUrl='$streamUrl', referer='$referer' -> proxiedUrl='$result'")
            return result
        }
    }

    private val embedExtractor by lazy { OmniEmbedExtractor(client, headers) }

    private fun verifyProxyManifest(proxyUrl: String): Boolean {
        Log.i(TAG, "verifyProxyManifest: [1/3] Waiting $PROXY_DELAY_MS ms before querying Watami proxy...")
        waitBeforeProxyRequest()

        val proxyHeaders = headers.newBuilder()
            .set("User-Agent", Miruro.USER_AGENT)
            .set("Accept", "*/*")
            .set("Referer", "https://strm.cx/")
            .set("Origin", "https://strm.cx")
            .build()

        val reqHeadersStr = proxyHeaders.joinToString(" | ") { "${it.first}: ${it.second}" }
        Log.i(TAG, "verifyProxyManifest: [2/3] GET $proxyUrl | Headers: [$reqHeadersStr]")

        return try {
            client.newCall(
                Request.Builder()
                    .url(proxyUrl)
                    .headers(proxyHeaders)
                    .get()
                    .build(),
            ).execute().use { response ->
                val code = response.code
                val respHeadersStr = response.headers.joinToString(" | ") { "${it.first}=${it.second}" }
                val body = response.body?.string().orEmpty()
                val hasExtM3u = body.contains("#EXTM3U")
                val valid = code == 200 && hasExtM3u

                Log.i(
                    TAG,
                    "verifyProxyManifest: [3/3] Result: HTTP $code, bodyLen=${body.length}, containsExtM3u=$hasExtM3u, isValid=$valid | Headers: [$respHeadersStr]",
                )
                if (body.isNotEmpty()) {
                    Log.d(TAG, "verifyProxyManifest: body preview (first 250 characters): ${body.take(250).replace("\n", "\\n")}")
                }

                if (!valid) {
                    Log.w(TAG, "verifyProxyManifest: Invalid or rejected manifest (HTTP $code) for url: $proxyUrl")
                }

                valid
            }
        } catch (error: Throwable) {
            Log.e(TAG, "verifyProxyManifest: EXCEPTION while verifying proxy at $proxyUrl: ${error.javaClass.simpleName}: ${error.message}", error)
            false
        }
    }

    /**
     * Dedicated HTTP/1.1 client for media / m3u8 fetches. Some provider CDNs
     * (notably Zoro's edge) reject HTTP/2 connections with the host app's
     * default OkHttp fingerprint by stamping a 444 status and closing the
     * socket. Forcing HTTP/1.1 + a 30 s read timeout (matching the proven
     * AnikotoTheme `m3u8Client` shape) avoids that fingerprint check.
     *
     * A [CloudflareInterceptor] is wired in to transparently solve Cloudflare
     * challenges for upstreams that WAF the m3u8 / segment URL (AnimePahe →
     * kwik.cx CDN is the canonical case — see [lib/kwikextractor] for the
     * precedent). The interceptor caches `cf_clearance` per host, so after
     * the first WebView solve the cached cookies clear subsequent requests
     * without burning another solve.
     */
    private val mediaClient by lazy {
        client.newBuilder()
            .readTimeout(30, TimeUnit.SECONDS)
            .protocols(listOf(Protocol.HTTP_2, Protocol.HTTP_1_1))
            .addInterceptor(CloudflareInterceptor(client))
            .build()
    }

    /**
     * Header-gated fallback leg: identical to [mediaClient] minus the
     * [CloudflareInterceptor]. Supplied to [M3u8Integration] / [m3u8Integration]
     * so that when the primary client's WebView solve fails (the canonical
     * crash chain: `vault-99.owocdn.top` returns 403 → CloudflareInterceptor
     * WebView solve produces no cookies → IOException propagates as 500 to
     * mpv), the m3u8 server retries through this client with whatever browser
     * headers the caller threaded via the proxied URL. Many header-gated
     * CDNs serve 200 to a plain HTTP/1.1 request with the correct Referer
     * once the WebView detour is bypassed.
     */
    private val mediaClientFallback by lazy {
        client.newBuilder()
            .readTimeout(30, TimeUnit.SECONDS)
            .protocols(listOf(Protocol.HTTP_2, Protocol.HTTP_1_1))
            .build()
    }

    private val m3u8Integration by lazy { M3u8Integration(mediaClient, mediaClientFallback) }

    private val megaCloudExtractor by lazy {
        MegaCloudExtractor(mediaClient, headers, MEGACLOUD_API_PLACEHOLDER)
    }

    private val rapidCloudExtractor by lazy {
        RapidCloudExtractor(mediaClient, headers, preferences)
    }

    private fun waitBeforeProxyRequest() {
        try {
            Thread.sleep(PROXY_DELAY_MS)
        } catch (_: InterruptedException) {
            Thread.currentThread().interrupt()
        }
    }

    fun providerDisplayName(key: String): String = resolveDisplayName(key)

    private fun resolveDynamicReferer(streamUrl: String, rawReferer: String): String {
        val trimmed = rawReferer.trim()
        if (trimmed.isNotEmpty()) {
            val parsedRef = trimmed.toHttpUrlOrNull()
            if (parsedRef != null) {
                return if (trimmed.endsWith("/")) trimmed else "$trimmed/"
            }
            return trimmed
        }

        val streamHttpUrl = streamUrl.toHttpUrlOrNull()
        val host = streamHttpUrl?.host?.lowercase().orEmpty()

        if (host.contains("owocdn.top")) {
            return KWIK_DEFAULT_REFERER
        }
        if (host.contains("miruro")) {
            return "${mirrorBaseUrl.trimEnd('/')}/"
        }

        return if (streamHttpUrl != null) {
            "${streamHttpUrl.scheme}://${streamHttpUrl.host}/"
        } else {
            "${mirrorBaseUrl.trimEnd('/')}/"
        }
    }

    fun decryptResponse(response: Response): String {
        if (!response.isSuccessful || response.code == 444 || response.code >= 500) {
            Log.w(TAG, "decryptResponse: Response HTTP ${response.code}, discarding response")
            return ""
        }

        val obfuscated = response.header("x-obfuscated") ?: "1"
        val bodyStr = response.body?.string()?.trim() ?: ""

        if (bodyStr.isEmpty() || bodyStr.startsWith("<")) {
            Log.w(TAG, "decryptResponse: Empty body or HTML error page (len=${bodyStr.length})")
            return ""
        }

        if (obfuscated != "2") {
            return bodyStr
        }

        return try {
            val cleaned = bodyStr.removeSurrounding("\"").trim()
            val decoded = runCatching { Base64.decode(cleaned, Base64.URL_SAFE) }
                .recoverCatching { Base64.decode(cleaned, Base64.DEFAULT) }
                .getOrElse { Base64.decode(cleaned, Base64.NO_PADDING or Base64.URL_SAFE) }

            val data = decoded.copyOf()
            for (i in data.indices) {
                data[i] = (data[i].toInt() xor pipeKey[i % pipeKey.size].toInt()).toByte()
            }

            val isGzip = data.size >= 2 && data[0] == 0x1F.toByte() && data[1] == 0x8B.toByte()
            val result = if (isGzip) {
                GZIPInputStream(java.io.ByteArrayInputStream(data)).use { gzipStream ->
                    gzipStream.bufferedReader(Charsets.UTF_8).readText()
                }
            } else {
                String(data, Charsets.UTF_8)
            }

            Log.d(TAG, "decryptResponse: Payload decrypted SUCCESSFULLY (${result.length} chars)")
            result
        } catch (e: Throwable) {
            Log.e(TAG, "decryptResponse: ERROR during decryption: ${e.javaClass.simpleName}: ${e.message}", e)
            ""
        }
    }

    fun parseStreamsFromResponse(
        response: Response,
        subType: String?,
        providerKey: String = "",
        episodeId: String = "",
        anilistId: String = "",
    ): List<Video> {
        Log.i(TAG, "parseStreamsFromResponse: Processing response for provider='$providerKey', subType='$subType', episodeId='$episodeId', anilistId='$anilistId'")

        val json = try {
            response.use(::decryptResponse)
        } catch (e: Throwable) {
            Log.e(TAG, "parseStreamsFromResponse: Exception during decryptResponse", e)
            return emptyList()
        }

        if (json.isEmpty()) {
            Log.w(TAG, "parseStreamsFromResponse: Decrypted JSON is empty, returning empty list")
            return emptyList()
        }

        val sourcesDto = try {
            SourcesResponseDto.parse(json)
        } catch (e: Throwable) {
            Log.e(TAG, "parseStreamsFromResponse: Error parsing JSON to SourcesResponseDto: ${json.take(400)}", e)
            return emptyList()
        }

        Log.i(
            TAG,
            "parseStreamsFromResponse: SourcesResponseDto parsed -> ${sourcesDto.streams.size} streams, ${sourcesDto.subtitles.size} subtitles",
        )
        sourcesDto.streams.forEachIndexed { i, s ->
            Log.i(TAG, "  stream[$i]: type='${s.type}', quality='${s.quality}', codec='${s.codec}', audio='${s.audio}', url='${s.url}', referer='${s.referer}'")
        }

        if (sourcesDto.streams.isEmpty()) {
            Log.w(TAG, "[FORENSIC] parseStreamsFromResponse: Empty 'streams' array in provider response (provider='$providerKey', subType='$subType', episodeId='$episodeId')")
            return emptyList()
        }

        val subTypeLabel = when (subType) {
            "sub" -> "Sub"
            "dub" -> "Dub"
            "ssub" -> "Soft Sub"
            "h-sub" -> "Hard Sub"
            null -> null
            else -> subType.replaceFirstChar { it.uppercase() }
        }

        val subtitles = sourcesDto.subtitles
            .filter { it.url.isNotEmpty() }
            .map { sub ->
                Track(sub.url, sub.label.ifEmpty { sub.language })
            }

        val videos = mutableListOf<Video>()
        val proxySeed = "$episodeId|$anilistId"

        for ((index, stream) in sourcesDto.streams.withIndex()) {
            if (stream.url.isEmpty()) {
                Log.w(TAG, "parseStreamsFromResponse: stream[$index] has empty URL, ignoring")
                continue
            }

            val qualityInt = stream.quality.filter { it.isDigit() }.toIntOrNull()
                ?: stream.resolution?.height?.takeIf { it > 0 }
                ?: 0
            val width = stream.resolution?.width ?: 0
            val height = stream.resolution?.height ?: 0
            val streamTypeLabel = stream.type.uppercase()

            val qualityLabel = buildString {
                if (providerKey.isNotEmpty()) append("${providerDisplayName(providerKey)} - ")
                if (qualityInt > 0) append("${qualityInt}p ")
                if (subTypeLabel != null) append("$subTypeLabel ")
                if (width > 0 && height > 0) append("(${width}x$height) ")
                if (stream.codec.isNotEmpty()) append("${stream.codec} ")
                if (stream.audio.isNotEmpty()) append("${stream.audio} ")
                if (stream.fansub.isNotEmpty()) append("${stream.fansub} ")
                append(streamTypeLabel)
            }.trim()

            Log.d(TAG, "parseStreamsFromResponse: stream#$index type=${stream.type} label=$qualityLabel url=${stream.url}")

            when (stream.type.lowercase()) {
                "hls" -> {
                    val rawUrl = stream.url.trim()
                    val videoUrl = when {
                        rawUrl.startsWith("//") -> "https:$rawUrl"
                        !rawUrl.startsWith("http", ignoreCase = true) -> "https://$rawUrl"
                        else -> rawUrl
                    }

                    val targetReferer = resolveDynamicReferer(videoUrl, stream.referer)
                    val proxiedUrl = buildProxiedUrl(videoUrl, targetReferer, proxyKey, proxySeed)
                    val finalUrl = proxiedUrl.ifEmpty { videoUrl }

                    val streamHeaders = if (finalUrl.contains("watami.win")) {
                        headers.newBuilder()
                            .set("User-Agent", Miruro.USER_AGENT)
                            .set("Accept", "*/*")
                            .set("Referer", "https://strm.cx/")
                            .set("Origin", "https://strm.cx")
                            .build()
                    } else {
                        headers.newBuilder()
                            .set("User-Agent", Miruro.USER_AGENT)
                            .set("Accept", "*/*")
                            .set("Accept-Language", "en-US,en;q=0.9")
                            .set("Referer", targetReferer)
                            .build()
                    }

                    Log.i(TAG, "parseStreamsFromResponse: ADDING HLS stream (Watami Proxy): $qualityLabel -> $finalUrl")

                    videos.add(
                        Video(
                            finalUrl,
                            qualityLabel,
                            finalUrl,
                            streamHeaders,
                            subtitleTracks = subtitles,
                        ),
                    )
                }
                "mp4" -> {
                    val rawUrl = stream.url.trim()
                    val videoUrl = when {
                        rawUrl.startsWith("//") -> "https:$rawUrl"
                        !rawUrl.startsWith("http", ignoreCase = true) -> "https://$rawUrl"
                        else -> rawUrl
                    }

                    val targetReferer = resolveDynamicReferer(videoUrl, stream.referer)
                    val streamHeaders = headers.newBuilder()
                        .set("User-Agent", Miruro.USER_AGENT)
                        .set("Accept", "*/*")
                        .set("Accept-Language", "en-US,en;q=0.9")
                        .set("Referer", targetReferer)
                        .build()

                    Log.i(TAG, "parseStreamsFromResponse: ADDING direct MP4 stream: $qualityLabel -> $videoUrl (Referer: $targetReferer)")

                    videos.add(
                        Video(
                            videoUrl,
                            qualityLabel,
                            videoUrl,
                            streamHeaders,
                            subtitleTracks = subtitles,
                        ),
                    )
                }
                "embed" -> {
                    if (stream.url.contains("kwik.cx")) {
                        Log.d(TAG, "parseStreamsFromResponse: Skipping kwik.cx embed")
                        continue
                    }
                    Log.i(TAG, "parseStreamsFromResponse: Extracting embed: ${stream.url}")
                    val embedVideos = extractPreRoutedEmbed(
                        embedUrl = stream.url,
                        qualityLabel = qualityLabel,
                        subtitles = subtitles,
                    )
                    if (embedVideos.isNotEmpty()) {
                        Log.i(TAG, "parseStreamsFromResponse: Embed extracted successfully (${embedVideos.size} videos found)")
                        videos.addAll(embedVideos)
                    } else {
                        Log.w(TAG, "parseStreamsFromResponse: Embed extraction failed for: ${stream.url}")
                    }
                }
                else -> {
                    Log.w(TAG, "parseStreamsFromResponse: Unknown stream type '${stream.type}', skipping: ${stream.url}")
                }
            }
        }

        Log.i(
            TAG,
            "parseStreamsFromResponse: FINISHED -> Returning ${videos.size} valid videos out of ${sourcesDto.streams.size} received",
        )
        return videos
    }

    private fun extractPreRoutedEmbed(
        embedUrl: String,
        qualityLabel: String,
        subtitles: List<Track>,
    ): List<Video> {
        val host = runCatching { embedUrl.toHttpUrlOrNull()?.host }.getOrNull()
        val lowerHost = host?.lowercase() ?: ""

        return when {
            MEGACLOUD_HOSTS.any { lowerHost.contains(it) } -> runCatching {
                megaCloudExtractor.getVideosFromUrl(
                    url = embedUrl,
                    type = "Multi",
                    name = qualityLabel,
                    withM3u8Server = false,
                )
            }.onFailure {
                Log.w(TAG, "MegaCloud extraction failed: ${it.message}")
            }.getOrDefault(emptyList())

            RAPID_CLOUD_HOSTS.any { lowerHost.contains(it) } -> runCatching {
                rapidCloudExtractor.getVideosFromUrl(embedUrl, type = "Multi", name = qualityLabel)
            }.onFailure {
                Log.w(TAG, "RapidCloud extraction failed: ${it.message}")
            }.getOrDefault(emptyList())

            else -> {
                embedExtractor.extractVideos(
                    embedUrl = embedUrl,
                    qualityLabel = qualityLabel,
                    subtitles = subtitles,
                )
            }
        }
    }
}

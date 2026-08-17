package eu.kanade.tachiyomi.animeextension.en.miruro

import android.util.Base64
import android.util.Log
import aniyomi.lib.megacloudextractor.MegaCloudExtractor
import aniyomi.lib.omniembedextractor.OmniEmbedExtractor
import aniyomi.lib.rapidcloudextractor.RapidCloudExtractor
import eu.kanade.tachiyomi.animesource.model.Track
import eu.kanade.tachiyomi.animesource.model.Video
import okhttp3.Headers
import okhttp3.HttpUrl.Companion.toHttpUrlOrNull
import okhttp3.OkHttpClient
import okhttp3.Request
import okhttp3.Response
import java.util.concurrent.ConcurrentHashMap
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

    companion object {
        private const val TAG = "MiruroExtractor"

        private val MEGACLOUD_HOSTS = listOf(
            "megacloud.tv",
            "megacloud.club",
            "megaplay.buzz",
            "rabbitstream.net",
            "dokicloud.one",
        )
        private val RAPID_CLOUD_HOSTS = listOf(
            "rapid-cloud.co",
            "scloud",
            "vidtube.site",
            "akirax.buzz",
        )

        private const val MEGACLOUD_API_PLACEHOLDER = "https://megacloud.example/decrypt/"
        internal const val KWIK_DEFAULT_REFERER = "https://kwik.cx/"
    }

    private val embedExtractor by lazy { OmniEmbedExtractor(client, headers) }
    private val subtitleAvailability = ConcurrentHashMap<String, Boolean>()

    private val megaCloudExtractor by lazy {
        MegaCloudExtractor(client, headers, MEGACLOUD_API_PLACEHOLDER)
    }

    private val rapidCloudExtractor by lazy {
        RapidCloudExtractor(client, headers, preferences)
    }

    fun providerDisplayName(key: String): String = resolveDisplayName(key)

    fun decryptResponse(response: Response): String {
        val obfuscated = response.header("x-obfuscated") ?: "1"
        val bodyStr = response.body?.string()?.trim() ?: ""

        Log.d(TAG, "=== DECRYPT RESPONSE ===")
        Log.d(TAG, "HTTP code: ${response.code}, x-obfuscated: $obfuscated, body length: ${bodyStr.length}")

        if (obfuscated != "2") {
            // Log.d(TAG, "Non-obfuscated body:\n$bodyStr")
            return bodyStr
        }

        if (bodyStr.isEmpty()) {
            Log.e(TAG, "Empty response body from server")
            return ""
        }

        return try {
            val cleaned = bodyStr.removeSurrounding("\"").trim()
            val decoded = runCatching { Base64.decode(cleaned, Base64.URL_SAFE) }
                .getOrElse { Base64.decode(cleaned, Base64.DEFAULT) }
            Log.d(TAG, "Step A: Base64 decoded (${decoded.size} bytes)")

            val data = decoded
            for (i in data.indices) {
                data[i] = (data[i].toInt() xor pipeKey[i % pipeKey.size].toInt()).toByte()
            }
            Log.d(TAG, "Step B: XOR applied with pipeKey (${data.size} bytes)")

            val result = try {
                GZIPInputStream(java.io.ByteArrayInputStream(data)).use { gzipStream ->
                    gzipStream.bufferedReader(Charsets.UTF_8).readText()
                }.also { Log.d(TAG, "Step C: Gzip decompression successful") }
            } catch (e: Exception) {
                Log.w(TAG, "Step C: Gzip decompression failed (${e.message}), trying plain UTF-8")
                String(data, Charsets.UTF_8)
            }

            // Log.d(TAG, "Decrypted JSON body (${result.length} chars):\n$result")
            result
        } catch (e: Exception) {
            Log.e(TAG, "Failed to decrypt response: ${e.message}", e)
            ""
        }
    }

    private fun availableSubtitles(
        subtitles: List<Track>,
        streamHeaders: Headers,
        videoUrl: String,
    ): List<Track> = subtitles.filter { subtitle ->
        val available = subtitleAvailability[subtitle.url] ?: run {
            val probeRequest = Request.Builder()
                .url(subtitle.url)
                .headers(
                    streamHeaders.newBuilder()
                        .set("Range", "bytes=0-0")
                        .build(),
                )
                .get()
                .build()

            val result = runCatching {
                client.newCall(probeRequest).execute().use { response ->
                    response.isSuccessful
                }
            }.onFailure { error ->
                Log.w(
                    TAG,
                    "Subtitle check failed for ${subtitle.url} " +
                        "(video=$videoUrl): ${error.javaClass.simpleName}: ${error.message}",
                )
            }.getOrDefault(false)

            subtitleAvailability[subtitle.url] = result
            result
        }

        if (!available) {
            Log.w(
                TAG,
                "Skipping unavailable subtitle '$subtitle' for $videoUrl: ${subtitle.url}",
            )
        }
        available
    }

    fun parseStreamsFromResponse(
        response: Response,
        subType: String?,
        providerKey: String = "",
        episodeId: String = "",
        anilistId: String = "",
    ): List<Video> {
        val json = try {
            response.use(::decryptResponse)
        } catch (e: Exception) {
            Log.e(TAG, "Failed to decrypt stream response: ${e.message}")
            return emptyList()
        }

        Log.d(TAG, "=== PARSE STREAMS ===")
        Log.d(TAG, "Provider: $providerKey, SubType: $subType, EpisodeId: $episodeId, AnilistId: $anilistId")

        val sourcesDto = try {
            SourcesResponseDto.parse(json)
        } catch (e: Exception) {
            Log.e(TAG, "Failed to parse sources JSON: ${e.message}")
            return emptyList()
        }

        Log.d(TAG, "Parsed Streams: ${sourcesDto.streams.size}, Subtitles: ${sourcesDto.subtitles.size}")

        if (sourcesDto.streams.isEmpty()) {
            Log.w(TAG, "Empty streams array in response (subType=$subType, provider=$providerKey)")
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
            .mapNotNull { sub ->
                val subUrl = sub.url.ifEmpty { sub.file }
                if (subUrl.isNotEmpty()) {
                    // Log.d(TAG, "    [Subtitle] URL: $subUrl | Lang: ${sub.language} | Label: ${sub.label}")
                    Track(subUrl, sub.label.ifEmpty { sub.language })
                } else {
                    null
                }
            }

        val videos = mutableListOf<Video>()

        for ((index, stream) in sourcesDto.streams.withIndex()) {
            if (stream.url.isEmpty()) continue

            val qualityInt = stream.quality.toIntOrNull() ?: 0
            val width = stream.resolution?.width ?: 0
            val height = stream.resolution?.height ?: 0
            val streamTypeLabel = stream.type.uppercase()

            val qualityLabel = buildString {
                if (providerKey.isNotEmpty()) append("${providerDisplayName(providerKey)} - ")
                if (stream.server.isNotEmpty()) append("${stream.server} ")
                if (qualityInt > 0) append("${qualityInt}p ")
                if (subTypeLabel != null) append("$subTypeLabel ")
                if (width > 0 && height > 0) append("${width}x$height ")
                if (stream.codec.isNotEmpty()) append("${stream.codec} ")
                if (stream.audio.isNotEmpty()) append("${stream.audio} ")
                if (stream.fansub.isNotEmpty()) append("${stream.fansub} ")
                append(streamTypeLabel)
            }.trim()

            Log.d(TAG, "--- Stream #$index ---")
            Log.d(TAG, "  Type: ${stream.type}")
            Log.d(TAG, "  URL: ${stream.url}")
            Log.d(TAG, "  Server: ${stream.server}")
            Log.d(TAG, "  QualityLabel: $qualityLabel")
            Log.d(TAG, "  Referer: ${stream.referer}")

            when (stream.type.lowercase()) {
                "hls", "mp4" -> {
                    val rawReferer = stream.referer.trim()
                    val targetReferer = if (rawReferer.isNotEmpty()) rawReferer else "${mirrorBaseUrl.trimEnd('/')}/"
                    val origin = targetReferer.toHttpUrlOrNull()?.let { "${it.scheme}://${it.host}" } ?: mirrorBaseUrl.trimEnd('/')
                    val streamHeaders = headers.newBuilder()
                        .set("User-Agent", Miruro.USER_AGENT)
                        .set("Referer", targetReferer)
                        .set("Origin", origin)
                        .build()

                    val videoUrl = stream.url
                    val availableSubtitles = availableSubtitles(
                        subtitles = subtitles,
                        streamHeaders = streamHeaders,
                        videoUrl = videoUrl,
                    )

                    videos.add(
                        Video(
                            videoUrl,
                            qualityLabel,
                            videoUrl,
                            streamHeaders,
                            subtitleTracks = availableSubtitles,
                        ),
                    )
                }
                "embed" -> {
                    if (stream.url.contains("kwik.cx")) {
                        Log.d(TAG, "  Skipped kwik.cx embed")
                        continue
                    }
                    Log.d(TAG, "  Extracting embed: ${stream.url}")
                    val embedVideos = extractPreRoutedEmbed(
                        embedUrl = stream.url,
                        qualityLabel = qualityLabel,
                        subtitles = subtitles,
                    )
                    Log.d(TAG, "  Embed extracted count: ${embedVideos.size}")
                    if (embedVideos.isNotEmpty()) {
                        videos.addAll(embedVideos)
                    } else {
                        Log.w(TAG, "  Failed to extract from embed: ${stream.url}")
                    }
                }
                else -> {
                    Log.w(TAG, "  Unknown stream type '${stream.type}', skipping: ${stream.url}")
                }
            }
        }

        Log.d(TAG, "Result: ${videos.size} total videos")
        for (v in videos) {
            Log.d(TAG, "  -> Video: ${v.quality} | URL: ${v.url}")
        }
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

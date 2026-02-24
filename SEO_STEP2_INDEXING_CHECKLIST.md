# SEO Adım 2 - Indexleme ve Doğrulama Checklist

Bu adımın hedefi: `qible.app` domaininin Google ve Bing tarafından doğrulanması, sitemap'in tanıtılması ve indexleme durumunun takip edilmesi.

## 1) Domain Tercihi ve Kural
- Tercih edilen host: `https://qible.app/`
- `www` sürümü tek yönlü 301 ile `qible.app`'e yönlenmeli.
- Canonical etiketi `https://qible.app/` olmalı (uygulandı).

## 2) Google Search Console
1. [Google Search Console](https://search.google.com/search-console) aç.
2. Property ekle:
   - Tercih: `Domain` property (`qible.app`)  -> DNS TXT ile doğrulama.
   - Alternatif: `URL-prefix` (`https://qible.app/`) -> meta tag veya HTML dosyası.
3. Eğer URL-prefix seçersen `google-site-verification` tokenını al.
4. Tokenı `public/index.html` içindeki şu alana yaz:
   - `<meta name="google-site-verification" content="REPLACE_WITH_GOOGLE_VERIFICATION_TOKEN">`
5. Deploy sonrası Verify butonuna bas.
6. Sol menüden Sitemaps bölümüne git ve şunu gönder:
   - `https://qible.app/sitemap.xml`

## 3) Bing Webmaster Tools
1. [Bing Webmaster Tools](https://www.bing.com/webmasters/) aç.
2. Site ekle: `https://qible.app/`
3. Doğrulama yöntemi:
   - Meta tag yöntemi seçersen tokenı al.
4. Tokenı `public/index.html` içindeki şu alana yaz:
   - `<meta name="msvalidate.01" content="REPLACE_WITH_BING_VERIFICATION_TOKEN">`
5. Deploy sonrası Verify butonuna bas.
6. Sitemap ekle:
   - `https://qible.app/sitemap.xml`

## 4) robots.txt ve sitemap Kontrolü
- `https://qible.app/robots.txt` yanıtı 200 olmalı.
- İçerikte şu satır bulunmalı:
  - `Sitemap: https://qible.app/sitemap.xml`
- `https://qible.app/sitemap.xml` yanıtı 200 olmalı ve parse hatası olmamalı.

## 5) Indexleme Sağlık Kontrolü
- GSC > Pages:
  - `Crawled - currently not indexed`
  - `Duplicate without user-selected canonical`
  - `Alternate page with proper canonical tag`
  - bu grupları haftalık izle.
- Hedef: Ana sayfa + kritik sayfalar `Indexed` durumunda.

## 6) İzleme Rutini (Haftalık)
- GSC Performance:
  - Query CTR
  - Ortalama pozisyon
  - En çok gösterim alan sorgular
- Bing Performance:
  - Query ve page trendleri
- Teknik:
  - 404 / soft-404 / redirect loop yok
  - canonical ve sitemap tutarlı

## 7) Deploy Sonrası Hızlı Test Komutları
```bash
curl -I https://qible.app/
curl -I https://qible.app/robots.txt
curl -I https://qible.app/sitemap.xml
curl -I https://www.qible.app/
```

## Not
Bu adım tamam sayılabilmesi için iki tokenın gerçek değerlerle doldurulup deploy edilmesi gerekir.

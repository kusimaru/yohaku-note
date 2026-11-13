const CACHE='yohaku-web-v78';
const ASSETS=['./','./index.html','./style.css','./app.mjs','./model.mjs','./storage.mjs','./richtext.mjs','./clip.mjs','./svgexport.mjs','./sync.mjs','./media.mjs','./ai.mjs','./pdf.mjs','./icon.svg','./manifest.webmanifest','./touch-test.html'].map(p=>new URL(p,self.location).href);
self.addEventListener('install',e=>{e.waitUntil(caches.open(CACHE).then(c=>c.addAll(ASSETS)).then(()=>self.skipWaiting()));});
self.addEventListener('activate',e=>{e.waitUntil(caches.keys().then(keys=>Promise.all(keys.filter(k=>k.startsWith('yohaku-')&&k!==CACHE).map(k=>caches.delete(k)))).then(()=>self.clients.claim()));});
// pdf.js (vendor/pdfjs) is loaded only when a PDF is used; once fetched it is kept (outside the versioned
// cache, so it survives app updates) and PDFs then work offline as well.
const PDFJS_CACHE='pdfjs-5.6.205';
self.addEventListener('fetch',e=>{
 const u=new URL(e.request.url);
 if(e.request.method!=='GET'||u.origin!==self.location.origin||!u.pathname.includes('/vendor/pdfjs/'))return;
 e.respondWith(caches.open(PDFJS_CACHE).then(c=>c.match(e.request,{ignoreSearch:true}).then(hit=>hit||fetch(e.request).then(res=>{if(res.ok)c.put(e.request,res.clone());return res;}))));
});
self.addEventListener('fetch',e=>{
 const url=new URL(e.request.url);url.search='';url.hash='';
 if(e.request.method!=='GET'||url.origin!==self.location.origin||!ASSETS.includes(url.href))return;
 // Always revalidate with the server when online (so a published update is picked up even if
 // the browser's HTTP cache still holds the old file), and refresh the offline copy.
 e.respondWith(fetch(url.href,{cache:'no-cache',credentials:'same-origin'}).then(res=>{if(res.ok)caches.open(CACHE).then(c=>c.put(e.request,res.clone()));return res;}).catch(()=>caches.match(e.request)));
});


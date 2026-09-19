const CACHE='yohaku-web-v4';
const ASSETS=['./','./index.html','./style.css','./app.mjs','./model.mjs','./storage.mjs','./richtext.mjs','./svgexport.mjs','./icon.svg','./manifest.webmanifest'].map(p=>new URL(p,self.location).href);
self.addEventListener('install',e=>{e.waitUntil(caches.open(CACHE).then(c=>c.addAll(ASSETS)));});
self.addEventListener('activate',e=>{e.waitUntil(caches.keys().then(keys=>Promise.all(keys.filter(k=>k.startsWith('yohaku-')&&k!==CACHE).map(k=>caches.delete(k)))).then(()=>self.clients.claim()));});
self.addEventListener('fetch',e=>{
 const url=new URL(e.request.url);url.search='';url.hash='';
 if(e.request.method!=='GET'||url.origin!==self.location.origin||!ASSETS.includes(url.href))return;
 e.respondWith(fetch(e.request).catch(()=>caches.match(e.request)));
});


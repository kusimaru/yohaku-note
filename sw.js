const CACHE='yohaku-web-v48';
const ASSETS=['./','./index.html','./style.css','./app.mjs','./model.mjs','./storage.mjs','./richtext.mjs','./svgexport.mjs','./sync.mjs','./media.mjs','./icon.svg','./manifest.webmanifest'].map(p=>new URL(p,self.location).href);
self.addEventListener('install',e=>{e.waitUntil(caches.open(CACHE).then(c=>c.addAll(ASSETS)).then(()=>self.skipWaiting()));});
self.addEventListener('activate',e=>{e.waitUntil(caches.keys().then(keys=>Promise.all(keys.filter(k=>k.startsWith('yohaku-')&&k!==CACHE).map(k=>caches.delete(k)))).then(()=>self.clients.claim()));});
self.addEventListener('fetch',e=>{
 const url=new URL(e.request.url);url.search='';url.hash='';
 if(e.request.method!=='GET'||url.origin!==self.location.origin||!ASSETS.includes(url.href))return;
 // Always revalidate with the server when online (so a published update is picked up even if
 // the browser's HTTP cache still holds the old file), and refresh the offline copy.
 e.respondWith(fetch(url.href,{cache:'no-cache',credentials:'same-origin'}).then(res=>{if(res.ok)caches.open(CACHE).then(c=>c.put(e.request,res.clone()));return res;}).catch(()=>caches.match(e.request)));
});


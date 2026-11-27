const scoreSlugs = ["qin-bingmayong", "taiyang-song", "siji-zuqu", "ganjiang-moye", "wusheng-zuqu", "caoyuan-kuangxiang", "guofeng", "yongheng-de-dongfeng", "dongbei-ensemble", "dongbei-orchestra", "dongbei-mixed", "la-la-land", "ganjie", "haohange", "huahaoyueyuan", "molihua", "ruoxuelinzhi"];
const oldSlug = location.hash.slice(1);
if (scoreSlugs.includes(oldSlug)) location.replace("/scores/work/" + oldSlug + "/");

/* Exact standalone audit. Run with node verify.cjs. No dependencies. */
const certificate=[
  {
    "v": 2,
    "sets": [
      [
        287,
        572,
        857,
        1142,
        1427,
        1712
      ],
      [
        316,
        630,
        944,
        1258,
        1572,
        1886
      ],
      [
        364,
        726,
        1088,
        1450,
        1812,
        2174
      ],
      [
        383,
        764,
        1145,
        1526,
        1907,
        2288
      ],
      [
        411,
        820,
        1229,
        1638,
        2047,
        2456
      ]
    ]
  },
  {
    "v": 619,
    "sets": [
      [
        597,
        608,
        630,
        641,
        652,
        663
      ],
      [
        431,
        478,
        525,
        572,
        666,
        713
      ],
      [
        457,
        511,
        565,
        673,
        727,
        781
      ],
      [
        164,
        255,
        346,
        437,
        528,
        710
      ],
      [
        517,
        721,
        823,
        925,
        1027,
        1129
      ]
    ]
  },
  {
    "v": 1236,
    "sets": [
      [
        1214,
        1225,
        1247,
        1258,
        1269,
        1280
      ],
      [
        1048,
        1095,
        1142,
        1189,
        1283,
        1330
      ],
      [
        1074,
        1128,
        1182,
        1290,
        1344,
        1398
      ],
      [
        781,
        872,
        963,
        1054,
        1145,
        1327
      ],
      [
        1134,
        1338,
        1440,
        1542,
        1644,
        1746
      ]
    ]
  },
  {
    "v": 1853,
    "sets": [
      [
        1831,
        1842,
        1864,
        1875,
        1886,
        1897
      ],
      [
        1665,
        1712,
        1759,
        1806,
        1900,
        1947
      ],
      [
        1691,
        1745,
        1799,
        1907,
        1961,
        2015
      ],
      [
        1398,
        1489,
        1580,
        1671,
        1762,
        1944
      ],
      [
        1751,
        1955,
        2057,
        2159,
        2261,
        2363
      ]
    ]
  },
  {
    "v": 2470,
    "sets": [
      [
        2448,
        2459,
        2481,
        2492,
        2503,
        2514
      ],
      [
        2282,
        2329,
        2376,
        2423,
        2517,
        2564
      ],
      [
        2308,
        2362,
        2416,
        2524,
        2578,
        2632
      ],
      [
        2015,
        2106,
        2197,
        2288,
        2379,
        2561
      ],
      [
        2368,
        2572,
        2674,
        2776,
        2878,
        2980
      ]
    ]
  },
  {
    "v": 3087,
    "sets": [
      [
        3065,
        3076,
        3098,
        3109,
        3120,
        3131
      ],
      [
        2899,
        2946,
        2993,
        3040,
        3134,
        3181
      ],
      [
        2925,
        2979,
        3033,
        3141,
        3195,
        3249
      ],
      [
        2632,
        2723,
        2814,
        2905,
        2996,
        3178
      ],
      [
        2985,
        3189,
        3291,
        3393,
        3495,
        3597
      ]
    ]
  },
  {
    "v": 3704,
    "sets": [
      [
        3422,
        3469,
        3516,
        3563,
        3610,
        3657
      ],
      [
        2456,
        2664,
        2872,
        3080,
        3288,
        3496
      ],
      [
        2288,
        2524,
        2760,
        2996,
        3232,
        3468
      ],
      [
        2174,
        2429,
        2684,
        2939,
        3194,
        3449
      ],
      [
        1886,
        2189,
        2492,
        2795,
        3098,
        3401
      ]
    ]
  }
];
function verify(cert){
const require=(x,m)=>{if(!x)throw Error(m)};
const p=617,N=3704;
function pow(a,b){let z=1n;for(;b;b>>=1n,a=a*a%617n)if(b&1n)z=z*a%617n;return z;}
function color(i){const r=(i-1)%p;return r===0?+(i===1):+(pow(BigInt(r),308n)===1n);}
require(cert.length===7,"seven witnesses");
const E=Array.from({length:7},(_,j)=>2+617*j);
require(new Set(cert.map(x=>x.v)).size===7&&cert.every(x=>E.includes(x.v)),"coverage");
for(const w of cert){
require(color(w.v)===1,"original violation");
require(w.sets.length===5,"five petals");
const seen=new Set();
for(const S of w.sets){
require(S.length===6,"six residual vertices");
for(const s of S){require(Number.isInteger(s)&&s>=1&&s<=N&&s!==w.v&&!seen.has(s),"disjoint");require(color(s)===0,"petal color");seen.add(s);}
const P=[...S,w.v].sort((a,b)=>a-b),d=P[1]-P[0];
require(d>0&&P.every((a,j)=>a===P[0]+j*d),"progression");
}
}
let count=0,bad=0;
const c=Array.from({length:N},(_,i)=>color(i+1));
for(let d=1;6*d<3703;d++)for(let a=0;a+6*d<3703;a++){
count++;let mono=true;for(let j=1;j<7;j++)if(c[a+j*d]!==c[a]){mono=false;break;}if(mono)bad++;
}
require(count===1140833&&bad===0,"baseline");
return {baselineProgressions:count,baselineViolations:bad,coveredFirstFlips:7,petalsPerFlip:5,minDistanceToAnyValid3704Coloring:6};
}
console.log(JSON.stringify(verify(certificate),null,2));
const corrupt=JSON.parse(JSON.stringify(certificate)); corrupt[0].sets[0][0]=2;
let rejected=false;try{verify(corrupt);}catch{rejected=true;}
if(!rejected)throw Error('negative control accepted');
console.log('negative control: rejected');

// The carver. Runs in a worker. Every piece is a signed distance field (centimetres, y up, the foot at y = 0),
// carved into a few thousand oriented Gaussian splats: flat discs lying on the surface, each with its own colour,
// opacity, material and normal. The page lights them every frame, so the gold really reflects as you turn it in your fingers.
'use strict';
const { abs, sqrt, min, max, sin, cos, atan2, floor, ceil, PI, exp, pow, sign } = Math;
const TAU = PI * 2;
const L2 = (x, y) => sqrt(x * x + y * y), L3 = (x, y, z) => sqrt(x * x + y * y + z * z);
const cl = (x, a, b) => x < a ? a : x > b ? b : x, mix = (a, b, t) => a + (b - a) * t, mod = (a, n) => a - n * floor(a / n);
const sst = (a, b, x) => { const t = cl((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); };
const smin = (a, b, k) => { const h = max(k - abs(a - b), 0) / k; return min(a, b) - h * h * k * .25; };
const smax = (a, b, k) => -smin(-a, -b, k);

// ── noise ──
function h3(i, j, k) { let n = Math.imul(i, 374761393) ^ Math.imul(j, 668265263) ^ Math.imul(k, 1274126177); n = Math.imul(n ^ (n >>> 13), 1274126177); return ((n ^ (n >>> 16)) >>> 0) / 4294967296; }
function vn(x, y, z) {
  const i = floor(x), j = floor(y), k = floor(z); let u = x - i, v = y - j, w = z - k; u = u * u * (3 - 2 * u); v = v * v * (3 - 2 * v); w = w * w * (3 - 2 * w);
  const a = mix(h3(i, j, k), h3(i + 1, j, k), u), b = mix(h3(i, j + 1, k), h3(i + 1, j + 1, k), u), c = mix(h3(i, j, k + 1), h3(i + 1, j, k + 1), u), d = mix(h3(i, j + 1, k + 1), h3(i + 1, j + 1, k + 1), u);
  return mix(mix(a, b, v), mix(c, d, v), w);
}
function fbm(x, y, z, o = 4) { let s = 0, a = .5; for (let i = 0; i < o; i++) { s += a * vn(x, y, z); x = x * 2.03 + 17.1; y = y * 2.03 + 3.7; z = z * 2.03 + 9.2; a *= .5; } return s / (1 - pow(.5, o)); }

// ── primitives ──
const sph = (x, y, z, r) => L3(x, y, z) - r;
function ell(x, y, z, a, b, c) { const k0 = L3(x / a, y / b, z / c), k1 = L3(x / (a * a), y / (b * b), z / (c * c)); return k1 < 1e-9 ? -min(a, b, c) : k0 * (k0 - 1) / k1; }
function box(x, y, z, a, b, c, r = 0) { const qx = abs(x) - a + r, qy = abs(y) - b + r, qz = abs(z) - c + r; return L3(max(qx, 0), max(qy, 0), max(qz, 0)) + min(max(qx, qy, qz), 0) - r; }
function box2(x, y, a, b, r = 0) { const qx = abs(x) - a + r, qy = abs(y) - b + r; return L2(max(qx, 0), max(qy, 0)) + min(max(qx, qy), 0) - r; }
function cylY(x, y, z, r, hh, rr = 0) { const dx = L2(x, z) - r + rr, dy = abs(y) - hh + rr; return min(max(dx, dy), 0) + L2(max(dx, 0), max(dy, 0)) - rr; }
const cylZ = (x, y, z, r, hh, rr = 0) => cylY(x, z, y, r, hh, rr);
const torY = (x, y, z, R, r) => L2(L2(x, z) - R, y) - r; // a ring lying flat
const torZ = (x, y, z, R, r) => L2(L2(x, y) - R, z) - r; // a ring standing up, facing you
function cap(x, y, z, ax, ay, az, bx, by, bz, r) {
  const px = x - ax, py = y - ay, pz = z - az, ex = bx - ax, ey = by - ay, ez = bz - az, h = cl((px * ex + py * ey + pz * ez) / (ex * ex + ey * ey + ez * ez), 0, 1);
  return L3(px - ex * h, py - ey * h, pz - ez * h) - r;
}
function rcone(x, y, z, ax, ay, az, bx, by, bz, r1, r2) { // a capsule whose radius runs from r1 at a to r2 at b
  const bax = bx - ax, bay = by - ay, baz = bz - az, l2 = bax * bax + bay * bay + baz * baz, rr = r1 - r2, a2 = l2 - rr * rr, il2 = 1 / l2;
  const pax = x - ax, pay = y - ay, paz = z - az, yv = pax * bax + pay * bay + paz * baz, zv = yv - l2;
  const qx = pax * l2 - bax * yv, qy = pay * l2 - bay * yv, qz = paz * l2 - baz * yv, x2 = qx * qx + qy * qy + qz * qz, y2 = yv * yv * l2, z2 = zv * zv * l2, k = sign(rr) * rr * rr * x2;
  if (sign(zv) * a2 * z2 > k) return sqrt(x2 + z2) * il2 - r2;
  if (sign(yv) * a2 * y2 < k) return sqrt(x2 + y2) * il2 - r1;
  return (sqrt(x2 * a2 * il2) + yv * rr) * il2 - r1;
}
function star5(px, py, r, rf) {
  const k1x = .809016994375, k1y = -.587785252292, k2x = -k1x, k2y = k1y;
  px = abs(px); let t = 2 * max(k1x * px + k1y * py, 0); px -= t * k1x; py -= t * k1y;
  t = 2 * max(k2x * px + k2y * py, 0); px -= t * k2x; py -= t * k2y; px = abs(px); py -= r;
  const bax = rf * -k1y, bay = rf * k1x - 1, hh = cl((px * bax + py * bay) / (bax * bax + bay * bay), 0, r);
  return L2(px - bax * hh, py - bay * hh) * sign(py * bax - px * bay);
}
let PX = 0, PZ = 0, PK = 0; // polar repetition around an axis: fold (x, z) into one of n sectors, centred on +x
function fold(x, z, n, off = 0) { const s = TAU / n, a = atan2(z, x) - off, k = Math.round(a / s), b = a - k * s, r = L2(x, z); PX = r * cos(b); PZ = r * sin(b); PK = k; }

// A lathe (surface of revolution) from a profile in the (radius, height) half plane. The profile is rounded by corner cutting
// (points flagged 1 stay sharp) and its 2D distance is tabulated once, so a lathe costs one bilinear lookup.
function chaikin(pts, it) {
  let p = pts.map(q => [q[0], q[1], q[2] || 0]); p[0][2] = p[p.length - 1][2] = 1;
  for (let k = 0; k < it; k++) {
    const o = [p[0]];
    for (let i = 0; i < p.length - 1; i++) {
      const a = p[i], b = p[i + 1];
      if (!a[2]) o.push([mix(a[0], b[0], .25), mix(a[1], b[1], .25), 0]);
      if (!b[2]) o.push([mix(a[0], b[0], .75), mix(a[1], b[1], .75), 0]); else o.push(b);
    }
    p = o;
  }
  return p;
}
function poly2(px, py, P) {
  const n = P.length; let d = (px - P[0][0]) ** 2 + (py - P[0][1]) ** 2, s = 1;
  for (let i = 0, j = n - 1; i < n; j = i, i++) {
    const vi = P[i], vj = P[j], ex = vj[0] - vi[0], ey = vj[1] - vi[1], wx = px - vi[0], wy = py - vi[1];
    const h = cl((wx * ex + wy * ey) / (ex * ex + ey * ey || 1), 0, 1), bx = wx - ex * h, by = wy - ey * h; d = min(d, bx * bx + by * by);
    const c1 = py >= vi[1], c2 = py < vj[1], c3 = ex * wy > ey * wx; if ((c1 && c2 && c3) || (!c1 && !c2 && !c3)) s = -s;
  }
  return s * sqrt(d);
}
function lathe(pts, it = 3, res = .016) {
  const P = chaikin(pts, it); let rmax = 0, ymin = 1e9, ymax = -1e9; for (const [r, y] of P) { rmax = max(rmax, r); ymin = min(ymin, y); ymax = max(ymax, y); }
  const pad = .35, y0 = ymin - pad, W = ceil((rmax + pad) / res) + 2, H = ceil((ymax - ymin + 2 * pad) / res) + 2, F = new Float32Array(W * H);
  for (let j = 0; j < H; j++) for (let i = 0; i < W; i++) F[j * W + i] = poly2(i * res, y0 + j * res, P);
  return (x, y, z) => {
    const r = L2(x, z), fx = r / res, fy = (y - y0) / res;
    if (fx >= W - 1 || fy < 0 || fy >= H - 1) return L2(max(r - rmax, 0), max(ymin - y, y - ymax, 0)) + .001; // outside the table: distance to its box, a lower bound
    const i = fx | 0, j = fy | 0, u = fx - i, v = fy - j, o = j * W + i;
    return mix(mix(F[o], F[o + 1], u), mix(F[o + W], F[o + W + 1], u), v);
  };
}

// ── materials (ids match the page's shader table) ──
const MAT = { gold: 0, silver: 1, bronze: 2, brass: 3, copper: 4, ebony: 5, ivory: 6, marbleW: 7, marbleB: 8, walnut: 9, jade: 10, malachite: 11, lapis: 12, ruby: 13, moonstone: 14,
  glass: 15, amber: 16, velvet: 17, porcelain: 18, lacquer: 19, flame: 20, milkglass: 21, sand: 22, filament: 23, roseQuartz: 24, ice: 25 };
const OPAC = { glass: .13, ice: .4, roseQuartz: .82, ruby: .9, amber: .86, flame: .82, milkglass: .9, moonstone: .97 };
let R = 0, G = 0, Bc = 0, OP = 1, EM = 0, MID = 0;
const set = (r, g, b) => { R = r; G = g; Bc = b; };
const mixc = (a, b, t) => set(mix(a[0], b[0], t), mix(a[1], b[1], t), mix(a[2], b[2], t));
function vein(x, y, z, f, w) { const v = abs(sin((x * .9 + y * .6 + z * .5) * f + fbm(x * .7 + 3, y * .7, z * .7) * 7)); return pow(1 - v, w); }
function paint(m, x, y, z, ao) {
  OP = 1; EM = 0; MID = m;
  const n1 = fbm(x * 1.7, y * 1.7, z * 1.7, 3);
  switch (m) {
    case MAT.gold: set(1, .7, .27); { const k = .9 + .1 * n1; R *= k; G *= k; Bc *= k; } break;
    case MAT.silver: set(.93, .93, .91); break;
    case MAT.bronze: { set(.72, .44, .21); const p = cl((.78 - ao) * 2.2, 0, 1) * (.5 + .5 * n1); mixc([R, G, Bc], [.1, .24, .19], p * .85); } break; // verdigris in the hollows
    case MAT.brass: set(.86, .7, .4); break;
    case MAT.copper: set(.93, .54, .4); break;
    case MAT.ebony: { const g = .5 + .5 * sin(y * 26 + fbm(x * 2, y * .5, z * 2, 3) * 9); set(.011 + .012 * g, .009 + .007 * g, .008 + .004 * g); } break;
    case MAT.ivory: { const g = fbm(x * 3, y * .8, z * 3, 3); set(.72 + .06 * g, .64 + .05 * g, .47 + .03 * g); } break;
    case MAT.marbleW: { const v = vein(x, y, z, 1.4, 22) * .85 + vein(x + 9, y, z - 4, 2.6, 40) * .5; set(.83, .82, .79); mixc([R, G, Bc], [.32, .33, .36], min(v, 1)); } break;
    case MAT.marbleB: { const v = vein(x, y, z, 1.2, 28) + vein(x - 5, y + 2, z, 2.4, 50) * .6; set(.011, .011, .013); mixc([R, G, Bc], [.62, .52, .36], min(v, 1)); } break;
    case MAT.walnut: { const t = L2(x + 4.3, z + 1.9) * 3.4 + fbm(x * .6, y * .9, z * .6) * 3.2 + y * .2, f = t - floor(t); const k = sst(.2, .9, f) * .6 + n1 * .4; set(mix(.06, .17, k), mix(.028, .08, k), mix(.014, .036, k)); } break;
    case MAT.jade: { const k = fbm(x * 1.4, y * 1.4, z * 1.4); set(mix(.03, .17, k), mix(.22, .5, k), mix(.1, .27, k)); const c = pow(vn(x * 3 + 5, y * 3, z * 3), 6) * .6; mixc([R, G, Bc], [.6, .75, .62], c); } break;
    case MAT.malachite: { const b = .5 + .5 * sin(L2(x - 2.2, y + 1.1) * 10 + fbm(x * .9, y * .9, z * .9) * 6); const k = pow(b, 3); set(mix(.004, .07, k), mix(.1, .48, k), mix(.04, .24, k)); } break;
    case MAT.lapis: { const k = fbm(x * 2.1, y * 2.1, z * 2.1); set(mix(.012, .05, k), mix(.025, .09, k), mix(.2, .5, k));
      if (h3(floor(x * 14), floor(y * 14), floor(z * 14)) < .045) { set(1, .72, .3); MID = MAT.gold; } // pyrite flecks
      const w = pow(vn(x * 1.2, y * 4, z * 1.2), 8); mixc([R, G, Bc], [.5, .55, .7], w * .5); } break;
    case MAT.ruby: set(.5 + .1 * n1, .005, .022); break;
    case MAT.moonstone: { set(.7, .74, .82); const k = n1; R *= .94 + .06 * k; G *= .95 + .05 * k; } break;
    case MAT.glass: set(.86, .93, 1); break;
    case MAT.amber: set(.7 + .1 * n1, .2 + .08 * n1, .012 + .01 * n1); EM = .06; break;
    case MAT.velvet: set(.3, .006, .02); break;
    case MAT.porcelain: set(.85, .85, .83); break;
    case MAT.lacquer: set(.006, .006, .008); break;
    case MAT.flame: set(1, .4, .05); EM = 1; break;
    case MAT.milkglass: set(.84, .87, .9); EM = .05; break;
    case MAT.sand: { const g = h3(floor(x * 40), floor(y * 40), floor(z * 40)); set(.7 * (.85 + .3 * g), .43 * (.85 + .3 * g), .15); } break;
    case MAT.filament: set(1, .55, .18); EM = 4; break;
    case MAT.roseQuartz: { const k = fbm(x * 1.3, y * 1.3, z * 1.3); set(.78 + .1 * k, .3 + .12 * k, .36 + .1 * k); } break;
    case MAT.ice: set(.62, .82, .96); break;
  }
  for (const k in OPAC) if (MAT[k] === m) OP = OPAC[k];
}

// ── the pedestal every piece stands on: a Staunton foot, bead, stem and collar ──
const PED = lathe([[0, 0, 1], [1.6, 0, 1], [1.74, .09], [1.76, .3], [1.64, .42, 1], [1.64, .48, 1], [1.68, .56], [1.6, .66, 1], [1.35, .74], [1.12, .9], [.95, 1.2], [.8, 1.7],
  [.68, 2.3], [.62, 2.72], [.66, 2.84, 1], [1.02, 2.92], [1.1, 3.02], [1.06, 3.12, 1], [.78, 3.18], [.56, 3.28], [0, 3.32, 1]], 3);
const PED_TOP = 3.26;
const P = (m, d, c) => ({ m: MAT[m], d, c });
function pedestal(base, accent, sy, sr) {
  const k = min(sy, sr);
  return [P(base, (x, y, z) => PED(x / sr, y / sy, z / sr) * k),
    P(accent, (x, y, z) => { x /= sr; y /= sy; z /= sr; return min(torY(x, y - .52, z, 1.668, .052), torY(x, y - 3.02, z, 1.088, .05)) * k; })];
}

// ── the pieces. Each `top(B)` gets B, the height of the collar, and returns its parts. ──
const MODELS = {
  crown: { base: 'ebony', accent: 'gold', top: B => { // KING
    const Rb = y => 1.02 + .16 * cl(y / 1.1, 0, 1);
    return [
      P('gold', (x, y, z) => { y -= B; const r = L2(x, z), Rr = Rb(y);
        let d = box2(r - Rr, y - .58, .085, .55, .04);
        fold(x, z, 8); const sp = rcone(PX, y, PZ, Rr + .02, .95, 0, Rb(1.1) + .12, 1.7, 0, .17, .05);
        d = smin(d, sp, .1); d = min(d, sph(PX - (Rb(1.1) + .13), y - 1.79, PZ, .12));
        d = min(d, max(min(torZ(x, y - 1.08, z, .99, .08), torZ(z, y - 1.08, x, .99, .08)), 1.1 - y)); // the arches
        d = min(d, sph(x, y - 2.22, z, .2), box(x, y - 2.56, z, .05, .2, .05, .024), box(x, y - 2.6, z, .16, .05, .05, .024)); // orb and cross
        d = min(d, torY(x, y - .07, z, Rb(.07) + .05, .065), torY(x, y - 1.06, z, Rb(1.06) + .05, .055));
        return d; }),
      P('velvet', (x, y, z) => { y -= B; return max(ell(x, y - .95, z, .96, .98, .96), .25 - y); }),
      P('ruby', (x, y, z) => { y -= B; fold(x, z, 8, PI / 8); return ell(PX - (Rb(.58) + .07), y - .58, PZ, .09, .15, .13); }),
    ]; } },

  key: { base: 'walnut', accent: 'brass', top: B => [ // KEY
    P('bronze', (x, y, z) => { y -= B;
      let d = cap(x, y, z, 0, .1, 0, 0, 2.3, 0, .14);
      d = smin(d, torY(x, y - 2.22, z, .2, .085), .05); d = smin(d, torY(x, y - 1.98, z, .17, .06), .04);
      const by = y - 3.02; d = min(d, torZ(x, by, z, .68, .12), torZ(x, by, z, .24, .07));
      { const a = atan2(by, x) - PI / 4, s = PI / 2, b = a - Math.round(a / s) * s, r = L2(x, by); d = min(d, cap(r * cos(b), r * sin(b), z, .24, 0, 0, .6, 0, 0, .055)); }
      { const a = atan2(by, x), s = PI / 2, b = a - Math.round(a / s) * s, r = L2(x, by); d = smin(d, sph(r * cos(b) - .84, r * sin(b), z, .11), .05); }
      let bit = box(x - .48, y - .58, z, .34, .36, .07, .025);
      bit = smax(bit, -box(x - .62, y - .62, z, .13, .07, .2), .02); bit = smax(bit, -box(x - .78, y - .36, z, .1, .1, .2), .02);
      return smin(d, bit, .04); }),
  ] },

  sun: { base: 'marbleW', accent: 'gold', top: B => [ // SUN
    P('gold', (x, y, z) => { const yy = y - (B + 1.92);
      let d = ell(x, yy, z, .92, .92, .36);
      const a = atan2(yy, x), s = TAU / 12, k = Math.round(a / s), b = a - k * s, r = L2(x, yy), L = (k & 1) ? 1.9 : 1.45;
      d = smin(d, rcone(r * cos(b), r * sin(b), z * 1.6, .75, 0, 0, L, 0, 0, .24, .035) / 1.35, .12);
      d = smin(d, torZ(x, yy, z - .31, .6, .045), .03); d = smin(d, sph(x, yy, z - .12, .3), .06);
      return d; }),
  ] },

  moon: { base: 'lapis', accent: 'silver', top: B => { // MOON
    const cres = (x, y) => max(L2(x, y) - 1.5, -(L2(x - .7, y + .08) - 1.3));
    return [
      P('moonstone', (x, y, z) => { const yy = y - (B + 1.72), c = cos(-.5), s = sin(-.5), xr = c * x - s * yy, yr = s * x + c * yy, d2 = cres(xr, yr);
        const hz = .07 + .3 * sst(0, -.55, d2), wx = d2 + .07, wy = abs(z) - hz; return min(max(wx, wy), 0) + L2(max(wx, 0), max(wy, 0)) - .07; }),
      P('silver', (x, y, z) => cylY(x + .3, y - (B + .14), z, .12, .22, .04)),
      P('gold', (x, y, z) => { const sx = x - .55, sy = y - (B + 3.0), sz = z - .1; return min(ell(sx, sy, sz, .07, .34, .07), ell(sx, sy, sz, .3, .07, .07)); }),
    ]; } },

  bell: { base: 'ivory', accent: 'bronze', sy: .92, top: B => { // BELL
    const F = lathe([[0, .16, 1], [1.28, .16], [1.52, .04, 1], [1.6, .12], [1.52, .3], [1.24, .66], [1.06, 1.15], [1.0, 1.6], [.94, 1.95], [.72, 2.18], [0, 2.26, 1]], 3);
    return [
      P('bronze', (x, y, z) => { y -= B; return min(F(x, y, z), torY(x, y - .4, z, 1.46, .045), torY(x, y - 1.86, z, .95, .04)); }),
      P('ebony', (x, y, z) => { y -= B; return smin(cylY(x, y - 2.45, z, .19, .25, .05), sph(x, y - 2.95, z, .33), .15); }),
    ]; } },

  flame: { base: 'marbleB', accent: 'brass', top: B => { // FIRE
    const cup = lathe([[0, 0, 1], [.45, 0], [.9, .18], [1.15, .42], [1.2, .52, 1], [1.08, .54, 1], [.85, .4], [0, .34, 1]], 2);
    const S = []; for (let i = 0; i <= 20; i++) { const t = i / 20; S.push([.24 * sin(t * 3.4) * t, .62 + t * 2.9, .1 * sin(t * 2.3 + 1) * t, .9 * pow(1 - t, .85) * (.78 + .22 * sin(PI * min(t * 1.6, 1))) + .03]); }
    const T = []; for (const sx of [-1, 1]) for (let i = 0; i <= 8; i++) { const t = i / 8; T.push([sx * (.42 + .32 * t - .15 * t * t), .75 + t * (sx > 0 ? 1.35 : 1.7), -.1, .42 * pow(1 - t, .9) + .03]); }
    return [
      P('brass', (x, y, z) => cup(x, y - B, z)),
      P('flame', (x, y, z) => { y -= B; let d = 1e9; for (const p of S) d = smin(d, sph(x - p[0], y - p[1], z - p[2], p[3]), .28);
        for (const p of T) d = smin(d, sph(x - p[0], y - p[1], z - p[2], p[3]), .2);
        return d + .05 * (vn(x * 2.5, y * 2.5, z * 2.5) - .5); }, (x, y, z) => { const t = cl((y - B - .2) / 3.3, 0, 1); set(1, mix(.12, .62, pow(t, .7)), mix(.005, .12, t * t)); EM = mix(.55, 1.05, t); }),
    ]; } },

  heart: { base: 'marbleW', accent: 'gold', top: B => [ // LOVE
    P('roseQuartz', (x, y, z) => { const yy = y - B, c = cos(.35), s = sin(.35), xr = c * x + s * z, zr = -s * x + c * z, px = abs(xr);
      const a = .6, ca = cos(a), sa = sin(a), lx = px - .6, ly = yy - 1.6, ex = ca * lx - sa * ly, ey = sa * lx + ca * ly;
      return ell(ex, ey, zr, .8, 1.2, .62); }),
  ] },

  umbrella: { base: 'porcelain', accent: 'silver', sy: .88, top: B => { // RAIN
    const drops = [[.75, 3.65, .45, .15], [-.95, 3.35, -.25, .13], [.15, 4.15, -.65, .12], [-.4, 4.4, .55, .1]];
    return [
      P('lacquer', (x, y, z) => { const yy = y - B, th = atan2(z, x), s2 = sin(4 * th) ** 2, Rr = 2.12 - .08 * s2;
        let d = abs(sph(x, yy - .95, z, Rr)) - (.055 + .045 * pow(1 - s2, 10));
        return smax(d, (1.98 + .2 * s2) - yy, .04); }),
      P('silver', (x, y, z) => { const yy = y - B; let d = cylY(x, yy - 1.55, z, .065, 1.6);
        d = min(d, rcone(x, yy, z, 0, 3.05, 0, 0, 3.52, 0, .1, .03));
        fold(x, z, 8); return min(d, sph(PX - 1.86, yy - 1.97, PZ, .07)); }),
      P('glass', (x, y, z) => { const yy = y - B; let d = 1e9; for (const [dx, dy, dz, r] of drops) d = min(d, smin(sph(x - dx, yy - dy, z - dz, r), rcone(x - dx, yy - dy, z - dz, 0, 0, 0, 0, r * 2.4, 0, r * .55, .01), r * .6)); return d; }),
    ]; } },

  hourglass: { base: 'walnut', accent: 'brass', sy: .85, top: B => [ // TIME
    P('walnut', (x, y, z) => { const yy = y - B; return min(cylY(x, yy - .12, z, 1.2, .12, .05), cylY(x, yy - 3.42, z, 1.2, .12, .05), sph(x, yy - 3.6, z, .16)); }),
    P('brass', (x, y, z) => { const yy = y - B; fold(x, z, 3, PI / 6); return min(cylY(PX - 1.0, yy - 1.77, PZ, .07, 1.6), sph(PX - 1.0, yy - 1.77, PZ, .12), torY(x, yy - .26, z, 1.12, .04), torY(x, yy - 3.28, z, 1.12, .04)); }),
    P('glass', (x, y, z) => { const yy = y - B; return abs(smin(sph(x, yy - .98, z, .8), sph(x, yy - 2.56, z, .8), .3)) - .045; }),
    P('sand', (x, y, z) => { const yy = y - B, r = L2(x, z);
      return min(max(sph(x, yy - .98, z, .73), yy - (.6 + .42 * max(0, 1 - r / .62))), max(sph(x, yy - 2.56, z, .73), yy - 2.28), cylY(x, yy - 1.45, z, .05, .6)); }),
  ] },

  anchor: { base: 'lapis', accent: 'silver', top: B => [ // SHIP
    P('silver', (x, y, z) => { const yy = y - B;
      let d = rcone(x, yy, z, 0, .4, 0, 0, 3.25, 0, .19, .13);
      d = min(d, torZ(x, yy - 3.55, z, .3, .085), cap(x, yy, z, -.95, 3.0, 0, .95, 3.0, 0, .1), sph(abs(x) - .98, yy - 3.0, z, .15));
      d = smin(d, smax(torZ(x, yy - 1.5, z, 1.2, .14), yy - 1.12, .04), .1);
      d = smin(d, rcone(abs(x), yy, z * 1.7, 1.13, 1.08, 0, 1.42, 1.62, 0, .3, .04) / 1.4, .06);
      return smin(d, sph(x, yy - .3, z, .2), .1); }),
  ] },

  bone: { base: 'walnut', accent: 'brass', top: B => [ // DOG
    P('ivory', (x, y, z) => { const yy = y - (B + .66), cy = cos(.5), sy = sin(.5), xr = cy * x + sy * z, zr = -sy * x + cy * z, cz = cos(.18), sz = sin(.18), x2 = cz * xr + sz * yy, y2 = -sz * xr + cz * yy;
      return smin(cap(x2, y2, zr, -1.05, 0, 0, 1.05, 0, 0, .3), sph(abs(x2) - 1.2, abs(y2) - .3, zr, .4), .25); }),
  ] },

  bulb: { base: 'ebony', accent: 'brass', top: B => [ // IDEA
    P('brass', (x, y, z) => { const yy = y - B; return cylY(x, yy - .55, z, .5 + .04 * sin(yy * 34), .5, .04); }),
    P('glass', (x, y, z) => { const yy = y - B, s = smin(cylY(x, yy - 1.25, z, .46, .3), sph(x, yy - 2.35, z, 1.08), .45); return max(abs(s) - .04, 1.02 - yy); }),
    P('brass', (x, y, z) => { const yy = y - B; return min(cap(abs(x), yy, z, .18, 1.0, 0, .32, 2.1, 0, .045), cylY(x, yy - 1.12, z, .2, .12, .04)); }),
    P('filament', (x, y, z) => { const yy = y - B; return cap(abs(x), yy, z, .32, 2.1, 0, 0, 2.45, 0, .065); }),
  ] },

  snail: { base: 'walnut', accent: 'copper', top: B => { // SLOW
    const S = []; for (let i = 0; i <= 36; i++) { const th = i / 36 * 3.6 * PI, g = exp(-.2 * th); S.push([-.15 + 1.0 * g * cos(th - PI / 2), 1.62 + 1.0 * g * sin(th - PI / 2), 0, .62 * g + .03]); }
    return [
      P('copper', (x, y, z) => { const yy = y - B; let d = 1e9; for (const p of S) d = smin(d, sph(x - p[0], yy - p[1], z - p[2], p[3]), .12); return d; },
        (x, y, z) => { const a = atan2(y - B - 1.62, x + .15), r = L2(x + .15, y - B - 1.62), t = mod(a + r * 9, TAU) / TAU; const k = .5 + .5 * sin(t * TAU * 3); set(mix(.5, .95, k), mix(.22, .55, k), mix(.14, .4, k)); }),
      P('jade', (x, y, z) => { const yy = y - B;
        let d = smin(ell(x + .1, yy - .3, z, 1.45, .3, .42), rcone(x, yy, z, 1.0, .4, 0, 1.45, 1.15, 0, .33, .25), .2);
        d = min(d, cap(x, yy, abs(z), 1.42, 1.25, .1, 1.7, 1.95, .24, .055), sph(x - 1.72, yy - 2.0, abs(z) - .25, .1));
        return d; }),
    ]; } },

  horseshoe: { base: 'malachite', accent: 'gold', top: B => [ // LUCK
    P('silver', (x, y, z) => { const yy = y - (B + 1.43), r = L2(x, yy);
      let d = smax(box2(r - 1.12, z, .27, .17, .07), yy - .62, .05);
      d = smax(d, -(L2(r - 1.12, z - .17) - .055), .02);
      for (const b of [.6, 1.05, 1.5]) { const hx = 1.12 * sin(b), hy = -1.12 * cos(b); d = smax(d, -min(cylZ(x - hx, yy - hy, z, .065, .5), cylZ(x + hx, yy - hy, z, .065, .5)), .02); }
      return d; }),
  ] },

  skep: { base: 'walnut', accent: 'gold', sy: .9, top: B => [ // HONEY
    P('amber', (x, y, z) => { const yy = y - B;
      let d = ell(x, yy, z, 1.42, 2.5, 1.42) - .05 * (.5 + .5 * cos(yy * TAU / .32));
      d = smax(d, -yy, .05); d = smax(d, -box(x, yy - .22, z - 1.35, .26, .22, .4, .12), .05);
      return smin(d, sph(x, yy - 2.5, z, .2), .1); }),
    P('amber', (x, y, z) => { const yy = y - B; return smin(sph(x - .02, yy - .2, z - 1.42, .09), rcone(x - .02, yy, z - 1.42, 0, -.05, 0, 0, .14, 0, .14, .06), .05); }), // a drip of honey
    P('ebony', (x, y, z) => { const bx = x - 1.0, by = y - B - 1.95, bz = z - .95; return min(ell(bx, by, bz, .27, .17, .17), sph(bx - .27, by + .02, bz + .05, .12)); },
      (x, y, z) => { const t = (x - 1.0) * 7; if (sin(t * PI) > .1 && x < 1.22) set(.9, .62, .12); }),
    P('glass', (x, y, z) => { const bx = x - .97, by = y - B - 2.2, bz = z - .95; return min(ell(bx + .1, by, bz + .14, .22, .04, .13), ell(bx + .1, by, bz - .14, .22, .04, .13)); }),
  ] },

  acorn: { base: 'jade', accent: 'gold', top: B => [ // OAK
    P('walnut', (x, y, z) => { const yy = y - B; return smin(ell(x, yy - 1.3, z, .8, 1.02, .8), rcone(x, yy, z, 0, .12, 0, 0, .55, 0, .05, .3), .25); }),
    P('bronze', (x, y, z) => { const yy = y - B, th = atan2(z, x);
      let d = max(sph(x, yy - 1.72, z, .9), 1.5 - yy) - .04 * cos(th * 16 + yy * 14) * cos(yy * 30);
      return min(d, cap(x, yy, z, 0, 2.5, 0, .12, 3.05, .05, .085)); }),
  ] },

  nose: { base: 'marbleB', accent: 'gold', top: B => [ // SMELL: a nose broken off a statue, far too big for its plinth
    P('marbleW', (x, y, z) => { const yy = y - B, fx = abs(x);
      let f = ell(x, yy - 1.5, z + .25, 1.0, 1.42, .62); f = smax(f, -(z + .5), .08);                 // the curve of a face, broken off flat behind
      f += .09 * (vn(x * 2.6 + 5, yy * 2.6, z * 2.6) - .5) * sst(.4, .9, L2(x / 1.0, (yy - 1.5) / 1.42)); // chipped round its edge
      f = smin(f, ell(fx - .46, yy - 2.48, z - .2, .46, .16, .24), .2);                                 // brows
      f = smin(f, ell(x, yy - .58, z - .22, .5, .17, .26), .15);                                        // a hint of upper lip
      let n = rcone(x, yy, z, 0, 2.6, .25, 0, 1.3, 1.08, .26, .34);
      n = smin(n, sph(x, yy - 1.15, z - 1.05, .4), .25);
      n = smin(n, ell(fx - .43, yy - .97, z - .7, .32, .27, .34), .2);
      n = smax(n, -ell(fx - .2, yy - .78, z - .9, .11, .08, .16), .05);
      return smin(f, n, .2); }),
  ] },

  rook: { base: 'marbleW', accent: 'gold', top: B => { // TOWER
    const F = lathe([[0, -.2, 1], [.98, -.2], [.9, .3], [.8, 1.5], [.84, 1.72], [1.06, 1.9], [1.1, 2.02, 1], [1.1, 2.8, 1], [0, 2.8, 1]], 3);
    return [
      P('marbleW', (x, y, z) => { const yy = y - B; let d = F(x, yy, z);
        fold(x, z, 6); d = smax(d, -box(PX - 1.0, yy - 2.68, PZ, .35, .25, .16), .03);
        return smax(d, -cylY(x, yy - 2.85, z, .74, .3), .03); }),
      P('gold', (x, y, z) => torY(x, y - B - 1.62, z, .82, .05)),
    ]; } },

  planet: { base: 'ebony', accent: 'gold', top: B => [ // SPACE
    P('lapis', (x, y, z) => sph(x, y - (B + 1.85), z, 1.08)),
    P('gold', (x, y, z) => { const yy = y - (B + 1.85), ca = cos(.42), sa = sin(.42), y1 = ca * yy - sa * z, z1 = sa * yy + ca * z, cb = cos(.28), sb = sin(.28), x2 = cb * x - sb * y1, y2 = sb * x + cb * y1, rr = L2(x2, z1);
      return smax(box2(rr - 1.72, y2, .4, .07, .03), -box2(rr - 1.55, y2, .03, .3), .01); }),
    P('gold', (x, y, z) => cylY(x, y - (B + .4), z, .13, .45, .03)),
    P('moonstone', (x, y, z) => sph(x - 1.75, y - (B + 3.15), z + .3, .2)),
  ] },

  notes: { base: 'ivory', accent: 'gold', top: B => [ // MUSIC
    P('lacquer', (x, y, z) => { const yy = y - B, c = cos(-.4), s = sin(-.4);
      const head = (cx, cy) => { const lx = x - cx, ly = yy - cy; return ell(c * lx - s * ly, s * lx + c * ly, z, .52, .37, .3); };
      return min(head(-.55, .38), head(.72, .88), cap(x, yy, z, -.1, .45, 0, -.1, 2.95, 0, .075), cap(x, yy, z, 1.17, .95, 0, 1.17, 3.35, 0, .075)); }),
    P('gold', (x, y, z) => { const yy = y - B, ang = atan2(.4, 1.27), c = cos(ang), s = sin(ang), lx = x - .535, ly = yy - 3.1; return box(c * lx + s * ly, -s * lx + c * ly, z, .72, .13, .12, .04); }),
  ] },

  crystal: { base: 'marbleW', accent: 'silver', top: B => { // COLD
    const X = [[0, 0, 0, 0, .42, 3.4], [.35, .2, .6, .45, .3, 2.4], [-.3, .25, 2.4, .5, .28, 2.0], [-.1, -.35, 4.0, .42, .3, 2.6], [.3, -.25, 5.3, .65, .22, 1.6]].map(([ox, oz, az, tl, Rr, L]) => {
      const a = [sin(tl) * cos(az), cos(tl), sin(tl) * sin(az)], t = abs(a[1]) < .9 ? [0, 1, 0] : [1, 0, 0];
      let u = [a[1] * t[2] - a[2] * t[1], a[2] * t[0] - a[0] * t[2], a[0] * t[1] - a[1] * t[0]]; const ul = L3(...u); u = u.map(v => v / ul);
      const v = [a[1] * u[2] - a[2] * u[1], a[2] * u[0] - a[0] * u[2], a[0] * u[1] - a[1] * u[0]];
      return { ox, oz, a, u, v, Rr, L, rot: az * 1.7 };
    });
    const sa = sin(.95), ca = cos(.95);
    return [P('ice', (x, y, z) => { const yy = y - B + .25; let d = 1e9;
      for (const c of X) { const px = x - c.ox, pz = z - c.oz, w = px * c.a[0] + yy * c.a[1] + pz * c.a[2], u = px * c.u[0] + yy * c.u[1] + pz * c.u[2], v = px * c.v[0] + yy * c.v[1] + pz * c.v[2];
        const s = PI / 3, a = atan2(v, u) + c.rot, b = a - Math.round(a / s) * s, f = L2(u, v) * cos(b);
        d = min(d, max(f - c.Rr, f * sa + (w - c.L) * ca, -w)); }
      return d; })]; } },

  padlock: { base: 'marbleB', accent: 'gold', top: B => [ // SAFE
    P('brass', (x, y, z) => { const yy = y - B; let d = box(x, yy - 1.0, z, 1.0, .92, .4, .3);
      return smax(d, -min(sph(x, yy - 1.12, z - .42, .15), box(x, yy - .88, z - .42, .065, .22, .15, .02)), .02); }),
    P('silver', (x, y, z) => { const yy = y - B; return min(smax(torZ(x, yy - 1.95, z, .66, .13), 1.95 - yy, .02), cylY(abs(x) - .66, yy - 1.85, z, .13, .14)); }),
  ] },

  ghost: { base: 'ebony', accent: 'silver', top: B => { // BOO
    const eyes = (x, y, z) => { const yy = y - B - .12, xs = x - .12 * sin(yy * 1.6); return min(ell(abs(xs) - .3, yy - 2.42, z - .86, .12, .19, .2), ell(xs, yy - 1.95, z - .9, .16, .22, .22)); };
    return [P('milkglass', (x, y, z) => { const yy = y - B - .12, xs = x - .12 * sin(yy * 1.6);
      let d = smin(sph(xs, yy - 2.25, z, .92), rcone(xs, yy, z, 0, 2.0, 0, 0, .45, 0, .92, 1.12), .3);
      d = smax(d, (.42 + .16 * sin(atan2(z, xs) * 5)) - yy, .06);
      d = smin(d, cap(abs(xs), yy, z, .75, 1.6, .1, 1.25, 2.05, .25, .2), .15);
      return smax(d, -eyes(x, y, z), .04); }, (x, y, z) => { if (eyes(x, y, z) < .05) { set(.012, .012, .016); OP = 1; EM = 0; } })]; } },

  star: { base: 'ebony', accent: 'silver', top: B => [ // STAR
    P('silver', (x, y, z) => { const yy = y - (B + 1.6), d2 = star5(x, -yy, 1.62, .46), k = .5; return max(d2, (abs(z) + k * d2) / sqrt(1 + k * k)); }),
  ] },

  apple: { base: 'ivory', accent: 'gold', top: B => { const cy = B + 1.12; return [ // APPLE
    P('ruby', (x, y, z) => { const yy = y - cy, th = atan2(z, x);
      let d = L3(x, yy * 1.06, z) - 1.15 - .035 * cos(th * 5) * sst(-.5, .8, yy);
      d = smax(d, -sph(x, yy - 1.2, z, .42), .32); return smax(d, -sph(x, yy + 1.22, z, .25), .2); }),
    P('bronze', (x, y, z) => cap(x, y - cy, z, 0, .75, 0, .14, 1.45, .03, .065)),
    P('jade', (x, y, z) => { const lx = x - .5, ly = y - cy - 1.28, lz = z - .05, c = cos(-.5), s = sin(-.5); return ell(c * lx - s * ly, s * lx + c * ly, lz, .55, .07, .26); }),
  ]; } },
};

// ── more helpers for the second set ──
const tint = (r, g, b) => () => set(r, g, b); // a part in its material, recoloured: red lacquer, yellow porcelain, green stems
let QX = 0, QY = 0; const rot = (x, y, a) => { const c = cos(a), s = sin(a); QX = c * x - s * y; QY = s * x + c * y; };
function tube(pts) { // a bent tube through [x, y, z, radius] points, tapering segment by segment
  let x0 = 1e9, x1 = -1e9, y0 = 1e9, y1 = -1e9, z0 = 1e9, z1 = -1e9;
  for (const [x, y, z, r] of pts) { x0 = min(x0, x - r); x1 = max(x1, x + r); y0 = min(y0, y - r); y1 = max(y1, y + r); z0 = min(z0, z - r); z1 = max(z1, z + r); }
  return (x, y, z) => {
    const bd = L3(max(x0 - x, x - x1, 0), max(y0 - y, y - y1, 0), max(z0 - z, z - z1, 0)); if (bd > .3) return bd;
    let d = 1e9; for (let i = 0; i < pts.length - 1; i++) { const a = pts[i], b = pts[i + 1]; d = min(d, rcone(x, y, z, a[0], a[1], a[2], b[0], b[1], b[2], a[3], b[3])); } return d;
  };
}
function pyr(x, y, z, s, h) { // a square pyramid: base side s on y = 0, apex at y = h
  x /= s; y /= s; z /= s; h /= s; const m2 = h * h + .25; x = abs(x); z = abs(z); if (z > x) { const t = x; x = z; z = t; } x -= .5; z -= .5;
  const qx = z, qy = h * y - .5 * x, qz = h * x + .5 * y, sq = max(-qx, 0), t = cl((qy - .5 * z) / (m2 + .25), 0, 1);
  const a = m2 * (qx + sq) * (qx + sq) + qy * qy, b = m2 * (qx + .5 * t) * (qx + .5 * t) + (qy - m2 * t) * (qy - m2 * t);
  return sqrt(((min(qy, -qx * m2 - qy * .5) > 0 ? 0 : min(a, b)) + qz * qz) / m2) * sign(max(qz, -y)) * s;
}
const ext = (d2, z, t, r) => L2(max(d2 + r, 0), max(abs(z) - t + r, 0)) + min(max(d2 + r, abs(z) - t + r), 0) - r; // a 2D shape extruded to half-thickness t, edges rounded by r
// a die: pips sunk in each face, opposite faces adding to seven
const PIPS = { 1: [[0, 0]], 2: [[-1, -1], [1, 1]], 3: [[-1, -1], [0, 0], [1, 1]], 4: [[-1, -1], [1, -1], [-1, 1], [1, 1]], 5: [[-1, -1], [1, -1], [0, 0], [-1, 1], [1, 1]], 6: [[-1, -1], [1, -1], [-1, 0], [1, 0], [-1, 1], [1, 1]] };
const PIPC = []; for (const [n, u, v, f] of [[[0, 1, 0], [1, 0, 0], [0, 0, 1], 1], [[0, -1, 0], [1, 0, 0], [0, 0, 1], 6], [[0, 0, 1], [1, 0, 0], [0, 1, 0], 2], [[0, 0, -1], [1, 0, 0], [0, 1, 0], 5], [[1, 0, 0], [0, 0, 1], [0, 1, 0], 3], [[-1, 0, 0], [0, 0, 1], [0, 1, 0], 4]])
  for (const [a, b] of PIPS[f]) PIPC.push([0, 1, 2].map(k => n[k] * 1.03 + (u[k] * a + v[k] * b) * .5));
const pips = (x, y, z) => { let d = 1e9; for (const [a, b, c] of PIPC) d = min(d, sph(x - a, y - b, z - c, .19)); return d; };

// ── the second set: fifty more. Literal ones for the early puzzles, associations, and the sly ones ──
Object.assign(MODELS, {
  egg: { base: 'walnut', accent: 'gold', top: B => { // EGG
    const cup = lathe([[0, 0, 1], [.5, 0], [.55, .1], [.32, .28], [.26, .5], [.42, .66], [.72, .9], [.86, 1.2], [.84, 1.28, 1], [.7, 1.14], [0, 1.08, 1]], 3);
    return [
      P('gold', (x, y, z) => cup(x, y - B, z)),
      P('porcelain', (x, y, z) => { const yy = y - B - 2.02, k = 1 - .12 * cl(yy / 1.12, -1, 1); return ell(x / k, yy, z / k, .8, 1.12, .8) * k; }, tint(.9, .84, .74)),
    ]; } },

  teacup: { base: 'walnut', accent: 'gold', top: B => { // TEA
    const saucer = lathe([[0, 0, 1], [.55, 0], [1.15, .1], [1.62, .26], [1.66, .33, 1], [1.52, .3], [1.1, .2], [.5, .16], [0, .16, 1]], 2);
    const cup = lathe([[0, .16, 1], [.36, .16], [.44, .25], [.62, .42], [.9, .85], [1.08, 1.42], [1.1, 1.5, 1], [0, 1.5, 1]], 3);
    const steam = [-1, 1].map(s => tube(Array.from({ length: 11 }, (_, i) => { const t = i / 10; return [s * .22 + .14 * sin(t * 6 + s), 1.75 + t * 1.6, 0, .075 - t * .03]; })));
    return [
      P('porcelain', (x, y, z) => { const yy = y - B; let d = smax(cup(x, yy, z), -ell(x, yy - 1.62, z, 1, 1, 1), .03); d = min(d, saucer(x, yy, z)); return smin(d, L2(L2(x - 1.2, yy - 1.0) - .3, z) - .08, .05); }, tint(.92, .91, .88)),
      P('lacquer', (x, y, z) => cylY(x, y - B - .95, z, .82, .03), tint(.25, .08, .012)),
      P('gold', (x, y, z) => torY(x, y - B - 1.5, z, 1.08, .035)),
      P('milkglass', (x, y, z) => min(steam[0](x, y - B, z), steam[1](x, y - B, z)), () => { OP = .4; EM = .15; }),
    ]; } },

  eye: { base: 'ebony', accent: 'gold', top: B => { const cy = B + 1.6; return [ // EYE
    P('porcelain', (x, y, z) => smin(sph(x, y - cy, z, 1.08), sph(x, y - cy, z - .6, .6), .22), (x, y, z) => {
      const yy = y - cy, l = L3(x, yy, z) || 1, ang = Math.acos(cl(z / l, -1, 1));
      if (ang < .2) set(.004, .004, .006);
      else if (ang < .5) { const s = .5 + .5 * sin(atan2(yy, x) * 38 + vn(x * 9, yy * 9, z * 9) * 5), t = (ang - .2) / .3; set(mix(.02, .07, s), mix(.1, .3, s) * (1 - .45 * t), mix(.38, .8, s) * (1 - .35 * t)); }
      else set(.93, .91, .88); }),
    P('gold', (x, y, z) => { const yy = y - B; fold(x, z, 3, -PI / 2); return min(cap(PX, yy, PZ, .18, .08, 0, .8, 1.15, 0, .075), cylY(x, yy - .12, z, .34, .12, .04)); }), // a three-pronged claw
  ]; } },

  cat: { base: 'marbleW', accent: 'gold', top: B => { // CAT
    const tail = tube([[-.55, .22, -.45, .13], [-.82, .2, -.05, .13], [-.72, .2, .4, .12], [-.35, .18, .7, .11], [.1, .18, .78, .1], [.45, .25, .62, .09], [.6, .4, .4, .08]]);
    return [P('lacquer', (x, y, z) => { const yy = y - B, fx = abs(x);
      let d = ell(x, yy - 1.0, z + .1, .76, 1.02, .68); d = smin(d, ell(x, yy - .32, z + .02, .92, .36, .8), .3);
      d = smin(d, cap(fx - .28, yy, z - .42, 0, .08, 0, 0, 1.1, -.04, .14), .14);
      const hy = yy - 2.3; let h = ell(x, hy, z - .02, .6, .5, .54); h = smin(h, ell(x, hy + .18, z - .42, .25, .17, .18), .12);
      h = smin(h, rcone(fx - .32, hy, z * 1.6, 0, .28, 0, .1, .82, -.05, .2, .03) / 1.3, .08);
      return min(smin(d, h, .18), tail(x, yy, z)); },
    (x, y, z) => { const hy = y - B - 2.3; if (z > .25 && L2((abs(x) - .22) / 1.5, hy - .06) < .085) { if (abs(abs(x) - .22) < .022) set(.01, .01, .01); else { set(1, .72, .22); MID = MAT.gold; } } })]; } },

  chili: { base: 'marbleB', accent: 'gold', top: B => { // HOT
    const body = tube(Array.from({ length: 15 }, (_, i) => { const t = i / 14; return [-.95 + 2.05 * t, .5 + 2.1 * pow(max(t - .6, 0), 1.6) - .1 * sin(t * PI), 0, .42 * pow(1 - t, .55) + .04]; }));
    return [
      P('lacquer', (x, y, z) => body(x, y - B, z), tint(.72, .03, .02)),
      P('lacquer', (x, y, z) => { const yy = y - B; return min(ell(x + 1.0, yy - .52, z, .16, .38, .38), cap(x, yy, z, -1.12, .52, 0, -1.45, .9, 0, .08)); }, tint(.12, .32, .06)),
    ]; } },

  dumbbell: { base: 'walnut', accent: 'silver', top: B => { const cy = B + 1.0; return [ // GYM
    P('silver', (x, y, z) => cap(x, y - cy, z, -1.55, 0, 0, 1.55, 0, 0, .11), tint(.72, .72, .75)),
    P('lacquer', (x, y, z) => { const yy = y - cy, fx = abs(x); return min(cylY(yy, fx - .95, z, .78, .1, .04), cylY(yy, fx - 1.18, z, .6, .09, .04), cylY(yy, fx - 1.36, z, .2, .07, .02)); }, tint(.05, .05, .055)),
    P('gold', (x, y, z) => { const yy = y - B; return smin(cylY(x, yy - .2, z, .3, .2, .05), cap(x, yy, z, 0, .3, 0, 0, cy - B - .1, 0, .12), .1); }),
  ]; } },

  trophy: { base: 'ebony', accent: 'gold', top: B => { // WIN
    const cup = lathe([[0, 0, 1], [.72, 0], [.72, .16], [.52, .22], [.46, .38, 1], [.28, .44], [.15, .6], [.13, 1.0], [.28, 1.16], [.82, 1.56], [.98, 2.2], [1.0, 2.55], [.93, 2.58, 1], [0, 2.46, 1]], 3);
    return [P('gold', (x, y, z) => { const yy = y - B; return smin(cup(x, yy, z), max(L2(L2(abs(x) - 1.02, yy - 2.0) - .32, z) - .07, .8 - abs(x)), .05); })]; } },

  scissors: { base: 'marbleB', accent: 'gold', top: B => { const py = 1.3; // CUT
    const half = (x, y, z, sx) => { const a = sx * .3, c = cos(a), s = sin(a), u = c * x + s * (y - py), v = -s * x + c * (y - py), w = z - sx * .05, t = cl(v / 2.25, 0, 1);
      const b = ext(max(abs(u + sx * .04) - .26 * (1 - t) - .02, -v, v - 2.25) * .9, w, .05, .015);
      return [b, min(cap(u, v, w, 0, 0, 0, 0, -.62, 0, .07), L2(L2(u, v + .95) - .3, w) - .075)]; };
    return [
      P('silver', (x, y, z) => min(half(x, y - B, z, 1)[0], half(x, y - B, z, -1)[0])),
      P('gold', (x, y, z) => min(half(x, y - B, z, 1)[1], half(x, y - B, z, -1)[1], cylZ(x, y - B - py, z, .1, .14, .03))),
    ]; } },

  question: { base: 'ebony', accent: 'gold', top: B => { const cy = 2.85, Rr = .62; return [ // WHY
    P('gold', (x, y, z) => { const yy = y - B, ay = yy - cy, zz = z * 1.1;
      let d = max(L2(L2(x, ay) - Rr, zz) - .18, -max(x, ay));                   // the hook, its lower left quarter missing
      d = min(d, sph(x + Rr, ay, zz, .18), cap(x, yy, zz, 0, cy - Rr, 0, 0, cy - Rr - .55, 0, .18));
      return min(d, sph(x, yy - .78, zz, .23), cylY(x, yy - .25, zz, .07, .3)) / 1.1; }),
  ]; } },

  fish: { base: 'lapis', accent: 'gold', top: B => { const cy = B + 1.72; // FISH
    const fin = (x, y, z, cx, cyy, a, rx, ry) => { rot(x - cx, y - cyy, a); return ell(QX, QY, z, rx, ry, .06); };
    return [
      P('copper', (x, y, z) => { const yy = y - cy, k = 1 - .38 * sst(-.2, 1.3, -x); return smax(ell(x, yy / k, z / k, 1.15, .68, .36) * k, -ell(x - 1.14, yy + .1, z, .1, .05, .2), .02); },
        (x, y, z) => { const yy = y - cy; set(1, .5 + .12 * sst(-.5, .4, -yy), .16 + .1 * sst(-.6, .2, -yy)); const sc = .5 + .5 * sin(x * 22 + abs(yy) * 9) * sin(yy * 22 - x * 6); R *= .9 + .1 * sc; G *= .88 + .12 * sc; }),
      P('amber', (x, y, z) => { const yy = y - cy; return min(fin(x, yy, z, -1.5, .3, .75, .55, .22), fin(x, yy, z, -1.5, -.3, -.75, .55, .22), fin(x, yy, z, -.1, .62, -.25, .5, .2), fin(x, yy, abs(z) - .3, .25, -.38, -.5, .28, .12)); }, tint(.95, .4, .06)),
      P('ebony', (x, y, z) => sph(x - .72, y - cy - .14, abs(z) - .26, .1)),
      P('silver', (x, y, z) => cylY(x, y - B - .5, z, .07, .55)),
    ]; } },

  lemon: { base: 'ebony', accent: 'gold', top: B => { const cy = B + .82; return [ // SOUR
    P('porcelain', (x, y, z) => { rot(x, y - cy, -.22); let d = ell(QX, QY, z, 1.02, .78, .78); d = smin(d, ell(QX - 1.0, QY, z, .3, .15, .15), .14); d = smin(d, ell(QX + 1.0, QY, z, .24, .14, .14), .14); return d + .02 * (vn(x * 7, y * 7, z * 7) - .5); }, tint(.97, .76, .05)),
    P('jade', (x, y, z) => { rot(x + .45, y - cy - .78, .5); return ell(QX, QY, z - .1, .52, .065, .22); }),
  ]; } },

  donut: { base: 'marbleW', accent: 'gold', top: B => { const cy = B + 1.32; // ZERO
    const SPR = [[.9, .2, .2], [.98, .85, .25], [.25, .6, .95], [.97, .97, .97], [.45, .82, .35]];
    return [
      P('walnut', (x, y, z) => torZ(x, y - cy, z, .8, .46), tint(.66, .38, .14)),
      P('porcelain', (x, y, z) => { const yy = y - cy; return smax(torZ(x, yy, z, .8, .5), .1 + .07 * sin(atan2(yy, x) * 7) - z, .05); },
        (x, y, z) => { const g = h3(floor(x * 8), floor(y * 8), floor(z * 8)); if (g < .14) set(...SPR[floor(g / .14 * 5)]); else set(.96, .5, .66); }),
    ]; } },

  pawn: { base: 'ivory', accent: 'gold', top: B => [P('ivory', (x, y, z) => { const yy = y - B; return smin(sph(x, yy - .98, z, .84), cylY(x, yy - .1, z, .44, .14, .05), .28); })] }, // PAWN

  house: { base: 'walnut', accent: 'gold', top: B => { // HOME
    const lit = (x, yy, z) => z > .66 && ((abs(x) < .2 && yy < .82) || (abs(abs(x) - .56) < .17 && abs(yy - .98) < .17));
    return [
      P('porcelain', (x, y, z) => { const yy = y - B; let d = box(x, yy - .76, z, .95, .76, .74, .04); d = smax(d, -box(x, yy - .4, z - .74, .2, .42, .07, .03), .02); return smax(d, -box(abs(x) - .56, yy - .98, z - .74, .17, .17, .06, .03), .02); },
        (x, y, z) => { if (lit(x, y - B, z)) { set(1, .7, .3); EM = .7; } else set(.92, .9, .85); }),          // the windows are lit
      P('lacquer', (x, y, z) => { const yy = y - B - 1.5; return ext(max((abs(x) + yy * 1.15 - 1.15) / 1.524, -yy), z, .88, .02); }, tint(.5, .07, .04)),
      P('lacquer', (x, y, z) => box(x - .5, y - B - 2.15, z + .2, .14, .4, .14, .02), tint(.42, .2, .14)),
    ]; } },

  cloud: { base: 'lapis', accent: 'silver', top: B => { // CLOUD
    const S = [[0, 1.55, 0, .72], [-.75, 1.25, .05, .55], [.78, 1.3, 0, .58], [-.32, 1.98, -.05, .52], [.38, 2.0, .05, .56], [-1.22, 1.08, 0, .38], [1.22, 1.12, .05, .4], [0, 1.15, .2, .55]];
    return [
      P('porcelain', (x, y, z) => { const yy = y - B; let d = 1e9; for (const [a, b, c, r] of S) d = smin(d, sph(x - a, yy - b, (z - c) * 1.3, r), .2); return smax(d / 1.15, .82 - yy, .1); }, tint(.95, .96, .98)),
      P('silver', (x, y, z) => cylY(x, y - B - .45, z, .09, .45)),
    ]; } },

  pyramid: { base: 'lapis', accent: 'gold', top: B => { // EGYPT
    const big = (x, yy, z) => pyr(x, yy, z + .15, 2.3, 2.05), small = (x, yy, z) => pyr(x + 1.05, yy, z - .7, 1.1, .98);
    return [
      P('sand', (x, y, z) => { const yy = y - B; return min(max(big(x, yy, z), yy - 1.62), small(x, yy, z)); }, (x, y, z) => { const k = .86 + .14 * (.5 + .5 * sin((y - B) * 22)); set(.8 * k, .64 * k, .4 * k); }), // courses of stone
      P('gold', (x, y, z) => { const yy = y - B; return max(big(x, yy, z), 1.62 - yy); }),                  // the gilded capstone
    ]; } },

  eiffel: { base: 'ebony', accent: 'gold', top: B => { // PARIS
    const W = yy => yy < 1.0 ? mix(.98, .4, pow(cl(yy, 0, 1), .75)) : yy < 2.4 ? mix(.4, .15, (yy - 1.0) / 1.4) : mix(.15, .035, cl((yy - 2.4) / 1.35, 0, 1));
    return [P('bronze', (x, y, z) => { const yy = y - B, fx = abs(x), fz = abs(z);
      let d = max((max(fx, fz) - W(yy)) * .8, yy - 3.85, -yy);
      d = smax(d, -min(L2(x / .5, max(yy, 0) / .62) - 1, L2(z / .5, max(yy, 0) / .62) - 1) * .45, .02);  // the great arches between the legs
      return min(d, box(x, yy - 1.02, z, .56, .05, .56, .01), box(x, yy - 2.4, z, .26, .045, .26, .01)); },
    (x, y, z) => { const yy = y - B, m = max(abs(x), abs(z)), h = abs(sin((yy + m) * 18)) * abs(sin((yy - m) * 18)), k = .65 + .35 * sst(.2, .6, h); R *= k; G *= k; Bc *= k; })]; } }, // iron lattice

  torii: { base: 'ebony', accent: 'gold', top: B => [ // JAPAN
    P('lacquer', (x, y, z) => { const yy = y - B, fx = abs(x);
      const d = min(rcone(fx, yy, z, .9, 0, 0, .84, 2.75, 0, .13, .11), box(x, yy - 2.2, z, 1.3, .085, .075, .02), box(x, yy - 2.5, z, .09, .24, .07, .02), box(x, yy - 2.72, z, 1.5, .07, .1, .02));
      return min(d, cylY(fx - .9, yy - .08, z, .19, .08, .03)); }, tint(.62, .07, .03)),
    P('lacquer', (x, y, z) => box(x, y - B - 2.88 - .06 * x * x, z, 1.62, .1, .13, .03), tint(.02, .02, .025)),   // the black top beam, ends sweeping up
  ] },

  witchhat: { base: 'ebony', accent: 'gold', top: B => { // WITCH
    const cone = tube([[0, .32, 0, .86], [0, .9, 0, .68], [.02, 1.5, 0, .5], [.1, 2.0, 0, .34], [.3, 2.5, 0, .2], [.62, 2.86, 0, .11], [.98, 2.96, 0, .055]]);
    return [
      P('lacquer', (x, y, z) => { const yy = y - B; return min(cone(x, yy, z), cylY(x, yy - .26 + .1 * pow(L2(x, z) / 1.8, 2), z, 1.8, .045, .035)); }, tint(.14, .05, .22)),
      P('gold', (x, y, z) => { const yy = y - B; return min(max(abs(L2(x, z) - .8) - .045, abs(yy - .55) - .13), max(box(x, yy - .55, z - .82, .17, .15, .05, .02), -box(x, yy - .55, z - .82, .09, .07, .2))); }),
    ]; } },

  globe: { base: 'walnut', accent: 'gold', top: B => { const cy = B + 2.0; return [ // WORLD
    P('lapis', (x, y, z) => sph(x, y - cy, z, 1.05), (x, y, z) => { rot(x, y - cy, .41); if (fbm(QX * 1.15 + 3.1, QY * 1.15 + .4, z * 1.15 - 2, 4) > .57) { set(1, .72, .3); MID = MAT.gold; } }), // gold continents on a lapis sea
    P('gold', (x, y, z) => { rot(x, y - cy, .41); return min(max(L2(L2(QY, z) - 1.17, QX) - .055, z - .15), sph(QX, abs(QY) - 1.2, z, .09)); }),
    P('gold', (x, y, z) => { const yy = y - B; return min(cylY(x, yy - .45, z, .09, .5), cylY(x, yy - .06, z, .55, .06, .03)); }),
  ]; } },

  phone: { base: 'ivory', accent: 'gold', top: B => { // HELLO
    const hand = tube([[-1.12, 1.45, 0, .24], [-.92, 1.62, 0, .16], [0, 1.74, 0, .15], [.92, 1.62, 0, .16], [1.12, 1.45, 0, .24]]);
    const dial = (x, y, z) => { const py = y - B - .62, pz = z - .7; return [py * .15 + pz * .99, py * .99 - pz * .15]; };   // the dial lies on the sloping front
    return [
      P('lacquer', (x, y, z) => { const yy = y - B; let d = box(x, yy - .55, z, 1.02 - .2 * yy, .52, .78 - .15 * yy, .16); d = min(d, cap(abs(x), yy, z, .58, .95, -.05, .62, 1.32, -.05, .09)); return min(d, hand(x, yy, z), ell(abs(x) - 1.12, yy - 1.36, z, .34, .2, .34)); }, tint(.02, .02, .025)),
      P('gold', (x, y, z) => { const [ax, ry] = dial(x, y, z); let d = ext(L2(x, ry) - .5, ax, .045, .015); for (let k = 0; k < 10; k++) { const a = -2.4 + k * .52; d = smax(d, -sph(x - .36 * cos(a), ry - .36 * sin(a), ax - .05, .08), .01); } return d; }),
      P('porcelain', (x, y, z) => { const [ax, ry] = dial(x, y, z); return ext(L2(x, ry) - .15, ax - .04, .03, .01); }, tint(.95, .93, .88)),
    ]; } },

  sheep: { base: 'lapis', accent: 'silver', top: B => { // SLEEP
    const W = []; for (let i = 0; i < 26; i++) { const u = h3(i, 3, 9) * 2 - 1, a = h3(i, 7, 1) * TAU, s = sqrt(1 - u * u); W.push([-.1 + .95 * s * cos(a), 1.32 + .62 * u, .62 * s * sin(a), .26 + .14 * h3(i, 5, 2)]); }
    const Z = (x, y, z, cx, cy, s) => { const lx = (x - cx) / s, ly = (y - cy) / s, lz = z / s; return min(cap(lx, ly, lz, -1, 1, 0, 1, 1, 0, .28), cap(lx, ly, lz, 1, 1, 0, -1, -1, 0, .28), cap(lx, ly, lz, -1, -1, 0, 1, -1, 0, .28)) * s; };
    return [
      P('ivory', (x, y, z) => { const yy = y - B; let d = ell(x + .1, yy - 1.32, z, .95, .62, .62); for (const [a, b, c, r] of W) d = smin(d, sph(x - a, yy - b, z - c, r), .1); return d; }, tint(.93, .9, .84)),
      P('lacquer', (x, y, z) => { const yy = y - B; let d = smin(ell(x - .98, yy - 1.5, z, .34, .4, .3), ell(x - .9, yy - 1.68, abs(z) - .3, .1, .2, .08), .05); return min(d, cap(abs(x + .1) - .5, yy, abs(z) - .3, 0, .9, 0, 0, .05, 0, .1)); }, tint(.05, .045, .045)),
      P('gold', (x, y, z) => { const yy = y - B; return min(Z(x, yy, z, 1.15, 2.45, .2), Z(x, yy, z, 1.55, 2.95, .16), Z(x, yy, z, 1.85, 3.4, .13)); }),   // zzz
    ]; } },

  lion: { base: 'marbleB', accent: 'gold', top: B => { const cy = B + 1.78; return [ // PRIDE
    P('gold', (x, y, z) => { const yy = y - cy, fx = abs(x); let f = ell(x, yy + .02, z - .15, .74, .8, .6);
      f = smin(f, ell(fx - .21, yy + .36, z - .62, .27, .22, .22), .12); f = smin(f, sph(fx - .56, yy - .68, z - .05, .2), .1);   // muzzle, ears
      return smax(f, -ell(fx - .27, yy - .14, z - .66, .11, .045, .1), .03); }),
    P('ebony', (x, y, z) => { const yy = y - cy; rot(x, yy + .12, 0); return min(ell(x, yy + .1, z - .76, .17, .11, .1), cap(x, yy, z, 0, -.2, .74, 0, -.38, .74, .035)); }),   // a dark nose and the line of the mouth
    P('bronze', (x, y, z) => { const yy = y - cy, a = atan2(yy, x), r = L2(x, yy); return min(L2(r - .98 - .06 * sin(a * 21) - .04 * sin(a * 7), z + .2) - .47, ell(x, yy, z + .32, 1.2, 1.24, .52)) + .03 * (vn(x * 6, yy * 6, z * 6) - .5); }, tint(.62, .3, .1)), // a full, soft mane
    P('gold', (x, y, z) => cylY(x, y - B - .3, z, .3, .35, .08)),
  ]; } },

  queen: { base: 'marbleW', accent: 'gold', sy: .95, top: B => { // QUEEN
    const F = lathe([[0, -.1, 1], [.56, -.1], [.5, .35], [.44, .9], [.58, 1.3], [.92, 1.72], [1.02, 1.84, 1], [.92, 1.92], [.5, 1.86], [0, 1.92, 1]], 3);
    return [
      P('marbleW', (x, y, z) => { const yy = y - B; let d = F(x, yy, z); fold(x, z, 9); d = smin(d, sph(PX - .95, yy - 1.95, PZ, .11), .04); return smin(d, sph(x, yy - 2.12, z, .24), .1); }),
      P('gold', (x, y, z) => torY(x, y - B - 1.1, z, .5, .05)),
    ]; } },

  cheese: { base: 'walnut', accent: 'gold', top: B => { // MOUSE
    const H = [[.25, .5, .55, .22], [-.45, .95, .3, .18], [.55, 1.08, -.05, .2], [-.15, .32, -.42, .16], [.05, 1.32, .5, .14], [-.8, .42, .1, .15], [.85, .45, .22, .16], [-.6, 1.25, -.2, .17]];
    const L = (x, z) => [cos(.55) * x + sin(.55) * z, -sin(.55) * x + cos(.55) * z];
    return [P('ivory', (x, y, z) => { const yy = y - B, [xr, zr] = L(x, z); let d = max(box(xr, yy - .72, zr, 1.25, .72, .95, .05), (abs(zr) + .38 * xr - .475) / 1.07);
      for (const [hx, hy, hz, hr] of H) d = smax(d, -sph(xr - hx, yy - hy, zr - hz, hr), .03); return d; }, (x, y, z) => { if (L(x, z)[0] < -1.18) set(.85, .5, .08); else set(.98, .78, .22); })];
  } },

  dove: { base: 'lapis', accent: 'gold', top: B => { const cy = B + 1.7; // PEACE
    const branch = tube([[1.15, .18, 0, .05], [1.05, -.15, .08, .05], [.85, -.4, .12, .045]]);
    return [
      P('porcelain', (x, y, z) => { const yy = y - cy, fz = abs(z); let d = smin(ell(x + .1, yy, z, .85, .44, .42), sph(x - .78, yy - .3, z, .3), .2);
        d = smin(d, ell(x + 1.0, yy + .02, z, .55, .09, .32), .15);
        const th = .95, w1 = (yy - .2) * sin(th) + (fz - .2) * cos(th), w2 = (yy - .2) * cos(th) - (fz - .2) * sin(th);
        return smin(d, ell(x + .05 - .25 * w1, w1 - .7, w2, .5, .78, .06), .1); }, tint(.95, .95, .93)),   // wings raised
      P('gold', (x, y, z) => rcone(x, y - cy, z, 1.02, .28, 0, 1.24, .22, 0, .07, .02)),
      P('jade', (x, y, z) => { const yy = y - cy; let d = branch(x, yy, z); for (const [lx, ly, lz] of [[1.08, -.05, .14], [.95, -.3, -.02], [.88, -.42, .2]]) d = min(d, ell(x - lx, yy - ly, z - lz, .15, .065, .08)); return d; }), // an olive branch
      P('ebony', (x, y, z) => sph(x - .92, y - cy - .38, abs(z) - .24, .07)),
      P('silver', (x, y, z) => cylY(x, y - B - .62, z, .07, .65)),
    ]; } },

  rocket: { base: 'marbleB', accent: 'silver', top: B => { // ROCKET
    const body = lathe([[0, .35, 1], [.42, .35], [.5, .62], [.55, 1.4], [.5, 2.4], [.38, 3.0], [.2, 3.4], [0, 3.62, 1]], 3);
    return [
      P('silver', (x, y, z) => body(x, y - B, z), (x, y, z) => { if (y - B > 2.75) { set(.8, .06, .05); MID = MAT.lacquer; } }),
      P('lacquer', (x, y, z) => { const yy = y - B; fold(x, z, 3, PI / 2); const t = cl((yy - .12) / 1.2, 0, 1); return ext(max(PX - (.5 + .58 * (1 - t)), yy - 1.32, .12 - yy) * .85, PZ, .055, .02); }, tint(.8, .06, .05)),
      P('lacquer', (x, y, z) => cylZ(x, y - B - 1.95, z - .5, .2, .09, .03), tint(.05, .15, .42)),
      P('silver', (x, y, z) => torZ(x, y - B - 1.95, z - .55, .22, .045)),
      P('flame', (x, y, z) => ell(x, y - B - .2, z, .26, .32, .26), () => { set(1, .55, .12); EM = 1.2; }),
    ]; } },

  guitar: { base: 'ebony', accent: 'gold', top: B => { // GUITAR
    const T = (x, y) => { rot(x, y, -.12); return [QX, QY]; };
    return [
      P('walnut', (x, y, z) => { const [u, v] = T(x, y - B); return smax(smin(ell(u, v - .88, z, .9, .82, .26), ell(u, v - 1.88, z, .68, .6, .26), .35), -cylZ(u, v - 1.55, z - .26, .25, .1), .02); },
        (x, y, z) => { const [u, v] = T(x, y - B); if (z > .14) { set(.78, .55, .28); const r = L2(u, v - 1.55); if (r > .27 && r < .36) set(.12, .06, .03); } }),   // a spruce top, a rosette round the hole
      P('ebony', (x, y, z) => { const [u, v] = T(x, y - B); return min(box(u, v - 3.0, z - .04, .11, .95, .08, .03), box(u, v - 4.18, z - .02, .17, .27, .06, .03), box(u, v - .55, z - .27, .32, .05, .04, .02)); }),
      P('gold', (x, y, z) => { const [u, v] = T(x, y - B); return min(sph(abs(u) - .22, v - 4.05, z, .07), sph(abs(u) - .22, v - 4.3, z, .07), box(u, v - 2.06, z - .13, .11, .02, .03)); }),
    ]; } },

  cherry: { base: 'marbleW', accent: 'gold', top: B => { // CHERRY
    const st = tube([[-.45, .98, 0, .065], [-.38, 1.6, 0, .062], [-.15, 2.2, 0, .06], [.05, 2.55, 0, .06]]), st2 = tube([[.5, .9, .12, .065], [.45, 1.5, .06, .062], [.25, 2.15, 0, .06], [.05, 2.55, 0, .06]]);
    const ch = (x, yy, z, cx, cyy, cz) => smax(sph(x - cx, yy - cyy, z - cz, .52), -sph(x - cx, yy - cyy - .56, z - cz, .14), .12);
    return [
      P('ruby', (x, y, z) => { const yy = y - B; return min(ch(x, yy, z, -.45, .52, 0), ch(x, yy, z, .5, .45, .12)); }),
      P('jade', (x, y, z) => { const yy = y - B; rot(x - .38, yy - 2.48, -.45); return min(st(x, yy, z), st2(x, yy, z), ell(QX, QY, z - .05, .5, .065, .22)); }, (x, y, z) => { if (y - B < 2.4) set(.25, .42, .12); }),
    ]; } },

  banana: { base: 'walnut', accent: 'gold', top: B => { // BANANA
    const T = tube(Array.from({ length: 17 }, (_, i) => { const t = i / 16, a = -.92 + 1.84 * t; return [2.05 * sin(a), .44 + 2.05 * (1 - cos(a)), 0, .37 * pow(sin(PI * (.05 + .9 * t)), .55) + .05]; }));
    return [P('porcelain', (x, y, z) => T(x, y - B, z), (x, y, z) => { if (abs(x) > 1.52) set(.22, .16, .06); else set(.97, .8, .16); })];
  } },

  sombrero: { base: 'walnut', accent: 'gold', top: B => { // MEXICO
    const brim = lathe([[0, .25, 1], [1.0, .3], [1.6, .42], [1.95, .62], [2.05, .76], [2.0, .82], [1.84, .68], [1.5, .52], [1.0, .44], [0, .42, 1]], 3);
    const crown = lathe([[0, .3, 1], [.64, .3], [.6, .9], [.52, 1.6], [.4, 1.96], [0, 2.08, 1]], 3);
    return [
      P('ivory', (x, y, z) => { const yy = y - B; return min(brim(x, yy, z), crown(x, yy, z)); }, (x, y, z) => { const yy = y - B, r = L2(x, z), a = atan2(z, x), w = .5 + .5 * sin(a * 26 + r * 9);
        set(.84 * (.85 + .15 * w), .68 * (.85 + .15 * w), .42 * (.8 + .2 * w)); if (r > 1.72 && yy > .5) set(...(sin(a * 16) > 0 ? [.72, .07, .05] : [.06, .45, .2])); }),  // woven straw, an embroidered rim
      P('gold', (x, y, z) => { const yy = y - B; return L2(max(abs(L2(x, z) - .63) - .04, 0), max(abs(yy - .52) - .13, 0)) - .015; }),
    ]; } },

  maple: { base: 'ebony', accent: 'gold', top: B => { const cy = B + 1.95; // CANADA
    const LOBES = [[0, 1], [.95, .82], [-.95, .82], [1.85, .52], [-1.85, .52]];
    const ang = (a, c) => abs(mod(a - c + PI, TAU) - PI);
    const rad = a => { let k = 0; for (const [c, w] of LOBES) k = max(k, w * pow(max(cos(ang(a, c) * 2.1), 0), 2.2)); return .42 + 1.08 * k + .05 * pow(abs(cos(a * 16)), 6) * k; };
    return [
      P('lacquer', (x, y, z) => { const yy = y - cy; return ext((L2(x, yy) - rad(atan2(x, yy))) * .55, z, .07, .035); },
        (x, y, z) => { const yy = y - cy, a = atan2(x, yy); let v = 1; for (const [c] of LOBES) v = min(v, ang(a, c) * L2(x, yy)); set(.72, .04, .03); if (v < .05) set(.45, .02, .02); }),   // red, with darker veins
      P('lacquer', (x, y, z) => cap(x, y - B, z, 0, .05, 0, 0, 1.6, 0, .07), tint(.4, .03, .02)),
    ]; } },

  dice: { base: 'walnut', accent: 'gold', top: B => { // CHANCE
    const D = (x, y, z, cy, a) => { const yy = y - B - cy, c = cos(a), s = sin(a); return [(c * x + s * z) / .62, yy / .62, (-s * x + c * z) / .62]; };
    const die = p => smax(box(p[0], p[1], p[2], 1, 1, 1, .22), -pips(p[0], p[1], p[2]), .04) * .62;
    return [P('ivory', (x, y, z) => min(die(D(x, y, z, .62, .5)), die(D(x, y, z, 1.86, -.35))), (x, y, z) => { for (const [cy, a] of [[.62, .5], [1.86, -.35]]) if (pips(...D(x, y, z, cy, a)) < .04) set(.02, .02, .025); })];
  } },

  cheers: { base: 'ebony', accent: 'gold', top: B => { // CHEERS
    const G = lathe([[0, 0, 1], [.62, 0], [.62, .06], [.14, .14], [.1, .95], [.3, 1.1], [.62, 1.4], [.72, 1.85], [.7, 2.4, 1], [0, 2.4, 1]], 3), k = .82;
    const glass = (x, y, z) => { let d = 1e9, w = 1e9; for (const sx of [-1, 1]) { rot(x - sx * 1.0, y - B, -sx * .19); const u = QX / k, v = QY / k, q = z / k, g = G(u, v, q);   // two glasses leaning in to touch
        d = min(d, max(g, -max(g + .045, 1.15 - v), v - 2.37) * k); w = min(w, max(g + .05, v - 1.72, 1.16 - v) * k); } return [d, w]; };
    return [P('glass', (x, y, z) => glass(x, y, z)[0]), P('ruby', (x, y, z) => glass(x, y, z)[1], tint(.42, .015, .04))];
  } },

  snowflake: { base: 'lapis', accent: 'silver', top: B => { const cy = B + 1.95; return [ // WINTER
    P('silver', (x, y, z) => { const yy = y - cy, a = atan2(yy, x) - PI / 6, s = PI / 3, b = a - Math.round(a / s) * s, r = L2(x, yy), px = r * cos(b), py = abs(r * sin(b));
      const d = min(cap(px, py, z, 0, 0, 0, 1.62, 0, 0, .085), cap(px, py, z, .62, 0, 0, .95, .36, 0, .065), cap(px, py, z, 1.06, 0, 0, 1.3, .24, 0, .06), cylZ(x, yy, z, .3, .07, .03));
      return min(smax(d, abs(z) - .09, .02), cylY(x, y - B - .15, z, .07, .15)); }),
  ]; } },

  knight: { base: 'marbleB', accent: 'gold', top: B => { const cy = B + 1.45; // KNIGHT
    const sh = (x, yy) => max(L2(x + 2.43, yy - 1.25) - 3.38, L2(x - 2.43, yy - 1.25) - 3.38, yy - 1.25);   // a heater shield
    const sword = (x, y, z) => { rot(x, y - B - 2.0, -.55); const u = QX, v = QY, w = z + .3, t = cl((-.2 - v) / 2.1, 0, 1);
      return [max(box(u, v + .2, w, .14 * (1 - t * .6), 1.95, .05, .02), -v - 2.1), min(box(u, v - 1.86, w, .55, .07, .07, .03), cap(u, v, w, 0, 1.9, 0, 0, 2.45, 0, .085), sph(u, v - 2.55, w, .14))]; };
    return [
      P('lapis', (x, y, z) => { const yy = y - cy; return ext(sh(x, yy), z + .22 * (x / .95) ** 2, .1, .03); },
        (x, y, z) => { const yy = y - cy; if (sh(x, yy) > -.12 || (abs(x) < .1 && yy > -.8 && yy < .95) || (abs(yy - .3) < .1 && abs(x) < .55)) { set(1, .72, .3); MID = MAT.gold; } }),   // a gold rim and cross
      P('silver', (x, y, z) => sword(x, y, z)[0]),
      P('gold', (x, y, z) => sword(x, y, z)[1]),
    ]; } },

  crystalball: { base: 'ebony', accent: 'gold', top: B => { const cy = B + 1.78; // FUTURE
    const stand = lathe([[0, 0, 1], [.75, 0], [.8, .12], [.55, .28], [.42, .55], [.6, .74], [.74, .8, 1], [0, .8, 1]], 3);
    return [
      P('glass', (x, y, z) => abs(sph(x, y - cy, z, 1.05)) - .035),
      P('milkglass', (x, y, z) => { const yy = y - cy, a = atan2(z, x) + yy * 2.4; return min((L2(L2(x, z) - .42 - .14 * sin(a * 2), yy * .8) - .26) * .75, sph(x, yy, z, .3)); }, () => { set(.62, .22, 1); EM = 1.1; OP = .8; }),  // a glowing swirl of mist inside
      P('gold', (x, y, z) => { const yy = y - B; fold(x, z, 3, PI / 2); return min(stand(x, yy, z), cap(PX, yy, PZ, .55, .72, 0, .78, 1.15, 0, .075)); }),
    ]; } },

  frog: { base: 'walnut', accent: 'gold', top: B => { // PRINCE
    const crown = (x, y, z) => { let d = box2(L2(x, z) - .3, y - .12, .045, .12, .02); fold(x, z, 5, PI / 2); return min(d, rcone(PX, y, PZ, .3, .2, 0, .33, .46, 0, .07, .03), sph(PX - .34, y - .5, PZ, .06)); };
    return [
      P('jade', (x, y, z) => { const yy = y - B, fx = abs(x);
        let d = smin(ell(x, yy - .72, z + .05, .95, .6, .85), ell(x, yy - 1.18, z - .3, .72, .44, .55), .3);
        d = smin(d, sph(fx - .38, yy - 1.52, z - .32, .27), .12); d = smin(d, ell(fx - .78, yy - .32, z + .2, .38, .3, .55), .2);
        d = smin(d, cap(fx, yy, z, .42, .55, .45, .52, .06, .76, .12), .1);
        return smax(d, -ell(x, yy - 1.02, z - .8, .5, .025, .22), .02); },
        (x, y, z) => { const yy = y - B; if (L3(abs(x) - .38, yy - 1.52, z - .32) < .3 && z > .44) { set(...(L2(abs(x) - .38, yy - 1.54) < .09 ? [.01, .01, .01] : [.95, .78, .2])); } else if (yy < .7 && z > .3) set(.55, .75, .4); }),
      P('gold', (x, y, z) => crown(x, y - B - 1.64, z + .1)),   // he is a prince, after all
    ]; } },

  butterfly: { base: 'ebony', accent: 'silver', top: B => { const cy = B + 2.0; // CHANGE
    const wing = (x, y, z) => { const yy = y - cy, fx = abs(x), u = fx * cos(.32) - z * sin(.32), w = fx * sin(.32) + z * cos(.32); rot(u - .82, yy - .42, -.5); const up = ell(QX, QY, w, .82, .62, .06); rot(u - .6, yy + .48, .45); return min(up, ell(QX, QY, w, .55, .44, .06)); };
    return [
      P('moonstone', wing, (x, y, z) => { const yy = y - cy, fx = abs(x); rot(fx - .82, yy - .42, -.5); const eu = L2(QX / .82, QY / .62); rot(fx - .6, yy + .48, .45); const e = min(eu, L2(QX / .55, QY / .44));
        if (e > .8) { set(.02, .02, .03); if (h3(floor(x * 6), floor(y * 6), 1) < .3) set(.9, .9, .9); } else set(mix(.05, .2, e), mix(.3, .7, e), mix(.85, 1, e)); }),   // morpho blue, black edges, white spots
      P('ebony', (x, y, z) => { const yy = y - cy; return min(ell(x, yy, z, .11, .72, .11), sph(x, yy - .78, z, .14), cap(abs(x), yy, z, .04, .85, 0, .34, 1.35, .05, .045), sph(abs(x) - .35, yy - 1.38, z - .05, .08)); }),
      P('silver', (x, y, z) => cylY(x, y - B - .62, z, .06, .65)),
    ]; } },

  penguin: { base: 'marbleW', accent: 'silver', top: B => [ // TUXEDO
    P('lacquer', (x, y, z) => { const yy = y - B; const d = smin(ell(x, yy - 1.22, z, .78, 1.18, .7), sph(x, yy - 2.42, z - .02, .5), .35); rot(abs(x) - .7, yy - 1.3, .25); return smin(d, ell(QX, QY, z + .05, .14, .66, .3), .08); },
      (x, y, z) => { const yy = y - B; if ((z > .12 && L2(x / .56, (yy - 1.12) / 1.0) < 1) || (z > .25 && L2(x / .3, (yy - 2.38) / .28) < 1)) set(.93, .93, .91);
        const e = L2(abs(x) - .2, yy - 2.55); if (z > .3 && e < .085) set(...(e < .045 ? [.01, .01, .01] : [.95, .95, .95])); }),   // a white shirt front
    P('amber', (x, y, z) => { const yy = y - B; return min(rcone(x, yy, z, 0, 2.38, .42, 0, 2.3, .8, .12, .03), ell(abs(x) - .3, yy - .06, z - .35, .26, .07, .26)); }, tint(1, .5, .05)),
    P('lacquer', (x, y, z) => { const yy = y - B - 2.0; return min(rcone(abs(x), yy, (z - .62) * 1.8, 0, 0, 0, .3, 0, 0, .06, .17) / 1.3, sph(x, yy, z - .62, .08)); }, tint(.7, .03, .03)), // and a bow tie
  ] },

  bishop: { base: 'ebony', accent: 'gold', top: B => [ // BISHOP
    P('ebony', (x, y, z) => { const yy = y - B; let d = smin(ell(x, yy - 1.25, z, .6, .98, .6), rcone(x, yy, z, 0, 1.9, 0, 0, 2.42, 0, .2, .06), .2);
      d = smin(d, cylY(x, yy - .14, z, .38, .2, .05), .2); rot(x, yy - 1.5, -.6); d = smax(d, -box(QX, QY - .3, z - .62, .055, .42, .6), .02);   // the mitre's cut
      return min(d, sph(x, yy - 2.52, z, .14)); }),
    P('gold', (x, y, z) => torY(x, y - B - .5, z, .4, .05)),
  ] },

  pumpkin: { base: 'walnut', accent: 'gold', top: B => { const cy = B + .98; return [ // PUMPKIN
    P('amber', (x, y, z) => { const yy = y - cy; const d = ell(x, yy, z, 1.3, .95, 1.3) + .1 * (1 - pow(abs(cos(atan2(z, x) * 4)), .5)) * (1 - pow(min(abs(yy) / .95, 1), 4)); return smax(d, -sph(x, yy - 1.0, z, .32), .25); }, tint(.95, .32, .02)),
    P('walnut', (x, y, z) => rcone(x, y - cy, z, 0, .7, 0, .16, 1.25, .04, .15, .1), tint(.28, .22, .08)),
  ]; } },

  snowman: { base: 'lapis', accent: 'silver', top: B => [ // SNOWMAN
    P('porcelain', (x, y, z) => { const yy = y - B; return smin(smin(sph(x, yy - .78, z, .8), sph(x, yy - 1.95, z, .6), .12), sph(x, yy - 2.85, z, .45), .1); }, tint(.96, .97, .99)),
    P('lacquer', (x, y, z) => { const yy = y - B; let d = min(cylY(x, yy - 3.47, z, .33, .3, .03), cylY(x, yy - 3.2, z, .52, .05, .02), sph(abs(x) - .16, yy - 2.95, z - .4, .075)); for (const by of [1.75, 2.05]) d = min(d, sph(x, yy - by, z - .57, .08)); return d; }, tint(.02, .02, .025)),
    P('amber', (x, y, z) => rcone(x, y - B, z, 0, 2.85, .4, .04, 2.8, .88, .1, .02), tint(1, .45, .05)),
    P('lacquer', (x, y, z) => min(torY(x, y - B - 2.42, z, .45, .1), cap(x, y - B, z, .3, 2.4, .35, .42, 1.95, .45, .08)), tint(.65, .05, .04)),
  ] },

  rainbow: { base: 'marbleW', accent: 'gold', top: B => { const cy = B + .3; // RAINBOW
    const COL = [[.85, .08, .08], [.95, .42, .04], [.98, .85, .1], [.18, .68, .22], [.08, .42, .9], [.28, .18, .72], [.55, .22, .78]];
    const CL = [[-1.3, .2, .05, .42], [-1.65, .05, -.05, .3], [-.95, .02, .1, .3], [1.3, .2, .05, .42], [1.65, .05, -.05, .3], [.95, .02, .1, .3]];
    return [
      P('porcelain', (x, y, z) => { const yy = y - cy; return max(box2(L2(x, yy) - 1.3, z, .5, .18, .06), -yy); }, (x, y, z) => set(...COL[cl(floor((1.8 - L2(x, y - cy)) * 7), 0, 6)])),
      P('porcelain', (x, y, z) => { const yy = y - cy; let d = 1e9; for (const [a, b, c, r] of CL) d = smin(d, sph(x - a, yy - b, z - c, r), .15); return d; }, tint(.96, .97, .99)),
    ]; } },

  diamond: { base: 'ebony', accent: 'silver', top: B => { const cy = B + 1.22; return [ // DIAMOND
    P('ice', (x, y, z) => { const yy = y - cy; fold(x, z, 8); const d = max(yy - .55, PX - 1.2, PX * .669 + yy * .743 - .877, PX * .7071 - yy * .7071 - .8485); fold(x, z, 8, PI / 8); return max(d, PX * .4 + yy * .917 - .8); }), // table, crown, girdle, pavilion, star facets
    P('silver', (x, y, z) => { fold(x, z, 4, PI / 4); return cap(PX, y - cy, PZ, .22, -1.2, 0, 1.12, .08, 0, .055); }),   // four prongs
  ]; } },

  infinity: { base: 'ebony', accent: 'gold', top: B => { const cy = B + 1.35; // FOREVER
    const T = tube(Array.from({ length: 49 }, (_, i) => { const t = i / 48 * TAU, s = sin(t), c = cos(t), k = 1 + s * s; return [1.55 * c / k, 1.55 * s * c / k, .22 * s, .17]; })); // a lemniscate, crossing over itself
    return [P('gold', (x, y, z) => min(T(x, y - cy, z), cylY(x, y - B - .62, z, .09, .62)))];
  } },

  yinyang: { base: 'marbleW', accent: 'gold', top: B => { const cy = B + 1.5, Rr = 1.15; return [ // BALANCE
    P('porcelain', (x, y, z) => cylZ(x, y - cy, z, Rr, .2, .1), (x, y, z) => { const v = (y - cy) / Rr, u = x / Rr; let dark = u < 0;
      if (L2(u, v - .5) < .5) dark = false; if (L2(u, v + .5) < .5) dark = true; if (L2(u, v - .5) < .14) dark = true; if (L2(u, v + .5) < .14) dark = false;
      if (dark) { set(.012, .012, .014); MID = MAT.lacquer; } else set(.93, .91, .87); }),
    P('gold', (x, y, z) => min(torZ(x, y - cy, z, Rr, .07), cylY(x, y - B - .2, z, .1, .2))),
  ]; } },

  thunder: { base: 'lapis', accent: 'gold', top: B => { // THUNDER
    const BOLT = [[.15, 2.75], [-.45, 1.3], [.05, 1.35], [-.3, .02], [.58, 1.62], [.06, 1.56], [.62, 2.75]];
    const S = [[0, 3.15, 0, .6], [-.72, 2.85, .05, .46], [.75, 2.9, 0, .48], [-.3, 3.5, -.05, .44], [.36, 3.55, .05, .46], [0, 2.8, .15, .5]];
    return [
      P('gold', (x, y, z) => ext(poly2(x, y - B, BOLT), z, .13, .05), () => { EM = .55; }),
      P('lacquer', (x, y, z) => { const yy = y - B; let d = 1e9; for (const [a, b, c, r] of S) d = smin(d, sph(x - a, yy - b, (z - c) * 1.2, r), .2); return d / 1.1; }, tint(.2, .21, .25)),  // a storm cloud
    ]; } },

  gift: { base: 'walnut', accent: 'gold', top: B => { // PRESENT
    const L = (x, y, z) => [cos(.4) * x + sin(.4) * z, y - B, -sin(.4) * x + cos(.4) * z];
    return [
      P('lacquer', (x, y, z) => { const [u, v, w] = L(x, y, z); return box(u, v - .85, w, .95, .85, .95, .06); }, tint(.04, .2, .4)),
      P('gold', (x, y, z) => { const [u, v, w] = L(x, y, z); let d = max(box(u, v - .85, w, .97, .87, .97, .06), min(abs(u) - .17, abs(w) - .17));   // ribbon
        for (const sx of [-1, 1]) { rot(u - sx * .3, v - 1.95, sx * .55); d = min(d, L2(L2(QX, QY) - .3, w * 1.4) / 1.4 - .065); }   // the bow
        return min(d, sph(u, v - 1.76, w, .15)); }),
    ]; } },

  alarm: { base: 'ebony', accent: 'gold', top: B => { const cy = B + 1.48; return [ // MORNING
    P('copper', (x, y, z) => { const yy = y - cy, fx = abs(x); return min(cylZ(x, yy, z, 1.0, .36, .12), cap(fx, yy, z, .55, -.75, 0, .8, -1.35, 0, .085), max(sph(fx - .6, yy - .95, z, .4), .75 - yy), cap(x, yy, z, 0, .95, 0, 0, 1.32, 0, .07), sph(x, yy - 1.36, z, .1)); }),
    P('porcelain', (x, y, z) => cylZ(x, y - cy, z - .35, .84, .04, .02), (x, y, z) => { const yy = y - cy, r = L2(x, yy), a = atan2(yy, x), s = PI / 6, b = a - Math.round(a / s) * s; set(.94, .92, .86);
      if (r > .66 && r < .78 && abs(b) * r < .04) set(.05, .05, .05);
      const seg = (dx, dy, len, w) => { const t = cl((x * dx + yy * dy) / len, 0, 1); return L2(x - dx * t * len, yy - dy * t * len) < w; };
      if (seg(0, 1, .6, .035) || seg(-.5, -.866, .42, .05) || r < .07) set(.04, .04, .04); }),   // seven o'clock
  ]; } },
});

// ── carving: find the surface on a voxel grid, pull each surface voxel onto it, make it a splat ──
const FLOATS = 20; // per splat: centre xyz, opacity | covariance xx xy xz yy | yz zz, random, material | albedo rgb, occlusion | normal xyz, emission
function carve(name, h = .09) {
  const M = MODELS[name], sy = M.sy || 1, sr = M.sr || 1, parts = [...pedestal(M.base, M.accent, sy, sr), ...M.top(PED_TOP * sy)], np = parts.length;
  let last = 0;
  const D = (x, y, z) => { let d = 1e9, pi = 0; for (let i = 0; i < np; i++) { const v = parts[i].d(x, y, z); if (v < d) { d = v; pi = i; } } last = pi; return d; };
  const x0 = -2.7, y0 = -.25, z0 = -2.7, C = 4, pts = []; let gx = 0, gy = 0, gz = 0, e = h * .25;
  const grad = (x, y, z) => {
    const a = D(x + e, y - e, z - e), b = D(x - e, y - e, z + e), c = D(x - e, y + e, z - e), d = D(x + e, y + e, z + e);
    gx = (a - b - c + d) / (4 * e); gy = (-a - b + c + d) / (4 * e); gz = (-a + b - c + d) / (4 * e);
  };
  // two passes: the pedestal at a coarser pitch, the carving on top finer, each keeping only the surface that belongs to it
  const pass = (h, keep) => {
    const hc = h * C, nx = ceil(5.4 / hc), ny = ceil(8.2 / hc), nz = ceil(5.4 / hc), thr = hc * .87 * 1.6 + h; e = h * .25;
    for (let k = 0; k < nz; k++) for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
      if (abs(D(x0 + (i + .5) * hc, y0 + (j + .5) * hc, z0 + (k + .5) * hc)) > thr) continue;
      for (let c = 0; c < C; c++) for (let b = 0; b < C; b++) for (let a = 0; a < C; a++) {
        let px = x0 + (i * C + a + .5) * h, py = y0 + (j * C + b + .5) * h, pz = z0 + (k * C + c + .5) * h, d = D(px, py, pz);
        if (abs(d) >= h * .5 || !keep(last)) continue;
        for (let it = 0; it < 3; it++) { grad(px, py, pz); const g2 = gx * gx + gy * gy + gz * gz || 1; px -= d * gx / g2; py -= d * gy / g2; pz -= d * gz / g2; d = D(px, py, pz); }
        if (abs(d) > h * .2 || py < -.02 || !keep(last)) continue;
        const part = last; grad(px, py, pz); const gl = sqrt(gx * gx + gy * gy + gz * gz) || 1;
        pts.push(px, py, pz, gx / gl, gy / gl, gz / gl, part, h);
      }
    }
  };
  pass(h * 1.15, p => p < 2); pass(h * .8, p => p >= 2);
  const n = pts.length / 8, out = new Float32Array(n * FLOATS);
  let top = 0, rad = 0;
  for (let s = 0; s < n; s++) {
    const q = s * 8, px = pts[q], py = pts[q + 1], pz = pts[q + 2], nx_ = pts[q + 3], ny_ = pts[q + 4], nz_ = pts[q + 5], part = parts[pts[q + 6]], hs = pts[q + 7];
    const st = .74 * hs * .01, sn = .13 * hs * .01, s2 = st * st, dn = sn * sn - s2;
    let occ = 0, w = 1; for (let i = 1; i <= 5; i++) { const t = .09 * i; occ += w * (t - D(px + nx_ * t, py + ny_ * t, pz + nz_ * t)); w *= .6; }
    const ao = cl(1 - 1.4 * occ, .08, 1);
    paint(part.m, px, py, pz, ao); if (part.c) part.c(px, py, pz);
    const o = s * FLOATS;
    out[o] = px * .01; out[o + 1] = py * .01; out[o + 2] = pz * .01; out[o + 3] = OP;
    out[o + 4] = s2 + dn * nx_ * nx_; out[o + 5] = dn * nx_ * ny_; out[o + 6] = dn * nx_ * nz_; out[o + 7] = s2 + dn * ny_ * ny_;
    out[o + 8] = dn * ny_ * nz_; out[o + 9] = s2 + dn * nz_ * nz_; out[o + 10] = h3(s, 77, 3); out[o + 11] = MID;
    out[o + 12] = R; out[o + 13] = G; out[o + 14] = Bc; out[o + 15] = ao;
    out[o + 16] = nx_; out[o + 17] = ny_; out[o + 18] = nz_; out[o + 19] = EM;
    top = max(top, py); rad = max(rad, L2(px, pz));
  }
  // shuffle-free: order does not matter, the page sorts every frame it needs to
  return { count: n, data: out, height: top * .01, radius: rad * .01 };
}

if (typeof module !== 'undefined') module.exports = { carve, MODELS };
else self.onmessage = ({ data }) => {
  const t0 = performance.now(), r = carve(data.name, data.h);
  self.postMessage({ id: data.id, name: data.name, count: r.count, data: r.data, height: r.height, radius: r.radius, ms: performance.now() - t0 }, [r.data.buffer]);
};

/*
 * Behavioural time-domain model of the two-transistor "Black regulator".
 *
 * This is not SPICE. Each part is reduced to the one or two behaviours that
 * matter for understanding the circuit:
 *   Q2 + zener  -> a comparator: Q2 conducts when V(Z) - V(out) > VBE_ON
 *   Q1          -> a switch with a saturation voltage, a storage-time delay,
 *                  and a collector-current ceiling set by its base drive x hFE
 *   C2 / C1     -> a capacitive divider: a step of dV at node A moves node Z
 *                  by dV * C2 / (C1 + C2)
 *   RZ          -> a current source recharging node Z toward Vin
 *   D1          -> a Schottky diode with a small resistive term
 *   L1, CLOAD   -> ideal parts plus DCR and ESR
 * Everything is integrated with a fixed time step (forward Euler).
 */
(function (root) {
  'use strict';

  var DEFAULTS = {
    vin: 14,        // V
    vz: 5.6,        // V   zener voltage
    rz: 1000,       // ohm
    c1: 47e-9,      // F
    c2: 4.7e-9,     // F
    r1: 1000,       // ohm Q1 base-emitter pull-up
    r2: 470,        // ohm Q1 base drive
    l: 220e-6,      // H
    dcr: 0.3,       // ohm inductor winding resistance
    cout: 220e-6,   // F
    esr: 0.1,       // ohm
    rload: 20,      // ohm
    hfe1: 80,       // Q1 current gain at high current
    hfe2: 200,      // Q2 current gain
    vbeOn: 0.62,    // Q2 switching threshold
    vbeClamp: 0.8,  // Q2 base-emitter clamp when hard on
    vebo: 5.5,      // Q2 emitter-base reverse breakdown
    tdOn: 0.10e-6,  // s  delay from Q2 deciding "on" to node A rising
    tdOff: 0.40e-6, // s  delay from Q2 deciding "off" to node A falling (Q1 storage time)
    dt: 0           // s  integration step (0 = choose automatically)
  };

  function simulate(params) {
    var p = {};
    for (var k in DEFAULTS) p[k] = DEFAULTS[k];
    for (k in params || {}) if (params[k] !== undefined) p[k] = params[k];

    var dt = p.dt || Math.min(10e-9, Math.max(2e-9, (p.vin + 0.4) * p.c2 / Math.max(1e-4, (p.vin - p.vz) / p.rz) / 400));
    var cz = p.c1 + p.c2;
    var kc = p.c2 / cz;
    var vth = p.vz - p.vbeOn; // nominal output

    // state
    var vz = 0, il = 0, vc = 0, s = 0, pend = -1, va = 0, t = 0;
    var startupPeak = 0, startupLimited = false;
    var reachedAt = -1, settle = 1.5e-3, maxT = 12e-3, recordLen = 1e-3;
    var warnVebo = false, warnLimit = false;

    var cap = Math.ceil(recordLen / dt) + 4;
    var rec = {
      t: new Float32Array(cap), va: new Float32Array(cap), vz: new Float32Array(cap),
      il: new Float32Array(cap), vo: new Float32Array(cap), s: new Uint8Array(cap)
    };
    var n = 0, recording = false, recStart = 0, endT = maxT;
    var acc = { pin: 0, pout: 0, pq1: 0, pd: 0, pl: 0, prz: 0, pdrive: 0, n: 0 };
    var strace = { t: [], vo: [], il: [] };
    var sEvery = Math.max(1, Math.round(10e-6 / dt)), sCount = 0;

    while (t < endT) {
      var vo = (vc + p.esr * il) / (1 + p.esr / p.rload);

      // Q1 base drive available from R2 (Q1 E-B 0.8 V, Q2 C-E 0.1 V, Q2 emitter at Vout)
      var idrive = Math.max(0, (p.vin - 0.8 - 0.1 - vo) / p.r2);
      var ib1 = Math.max(0, idrive - 0.8 / p.r1);
      var ilim = p.hfe1 * ib1;

      // node A and inductor
      var vaNew, limited = false;
      if (s) {
        vaNew = p.vin - (0.12 + 0.35 * Math.max(il, 0));
        var dil = (vaNew - vo - il * p.dcr) / p.l * dt;
        if (il + dil > ilim) {
          // Q1 runs out of base drive and leaves saturation: it holds the current
          // at its ceiling, node A sags until the inductor voltage matches.
          limited = true;
          var ilNew = Math.max(ilim, il - (vo + 0.3 + il * p.dcr) / p.l * dt);
          vaNew = Math.max(-0.3, vo + il * p.dcr + (ilNew - il) * p.l / dt);
          il = ilNew;
        } else {
          il += dil;
        }
      } else {
        if (il > 0) {
          vaNew = -(0.30 + 0.12 * il);
          il += (vaNew - vo - il * p.dcr) / p.l * dt;
          if (il < 0) il = 0;
        } else {
          il = 0;
          vaNew = vo; // discontinuous mode: node A floats to Vout (ringing ignored)
        }
      }
      if (limited) { if (recording) warnLimit = true; else if (reachedAt < 0) startupLimited = true; }

      // capacitive coupling of node A's movement into node Z through C2
      vz += (vaNew - va) * kc;
      va = vaNew;

      // RZ recharges node Z; Q2 base current comes out of it while on
      var irz = (p.vin - vz) / p.rz;
      var ib2 = s ? idrive / p.hfe2 : 0;
      vz += (irz - ib2) / cz * dt;

      // clamps on node Z
      if (vz > p.vz) vz = p.vz;                              // zener
      if (s && vz > vo + p.vbeClamp) vz = vo + p.vbeClamp;     // Q2 B-E forward
      if (vz < -0.7) vz = -0.7;                              // zener forward
      if (vz < vo - p.vebo) { vz = vo - p.vebo; if (recording) warnVebo = true; }

      // output capacitor: inductor current plus Q2 emitter current (Q1's base drive) feed it
      var iin2out = il + (s ? idrive + ib2 : 0);
      vc += (iin2out - vo / p.rload) / p.cout * dt;

      // comparator with delays
      var want = (vz - vo) > p.vbeOn ? 1 : 0;
      if (want !== s) {
        if (pend < 0) pend = want ? p.tdOn : p.tdOff;
        pend -= dt;
        if (pend <= 0) { s = want; pend = -1; }
      } else pend = -1;

      if (reachedAt < 0) {
        if (il > startupPeak) startupPeak = il;
        if (vo >= vth - 0.02) { reachedAt = t; endT = Math.min(maxT, t + settle + recordLen); }
      }

      if (sCount++ % sEvery === 0) { strace.t.push(t); strace.vo.push(vo); strace.il.push(il); }

      if (!recording && reachedAt >= 0 && t >= endT - recordLen) { recording = true; recStart = t; }
      if (!recording && reachedAt < 0 && t >= maxT - recordLen) { recording = true; recStart = t; }
      if (recording && n < cap) {
        rec.t[n] = t - recStart; rec.va[n] = va; rec.vz[n] = vz; rec.il[n] = il; rec.vo[n] = vo; rec.s[n] = s;
        n++;
        var vd = (!s && il > 0) ? -va : 0;
        acc.pin += p.vin * ((s ? il + idrive + ib2 : 0) + irz);
        acc.pout += vo * vo / p.rload;
        acc.pq1 += s ? (p.vin - va) * il : 0;
        acc.pd += vd * il;
        acc.pl += il * il * p.dcr;
        acc.prz += irz * (p.vin - vz) + irz * vz; // RZ + zener
        acc.pdrive += s ? idrive * (p.vin - vo) : 0;
        acc.n++;
      }
      t += dt;
    }

    // statistics over the recorded window
    var edges = [], falls = [];
    for (var i = 1; i < n; i++) {
      if (rec.s[i] && !rec.s[i - 1]) edges.push(i);
      if (!rec.s[i] && rec.s[i - 1]) falls.push(i);
    }
    var f = 0, duty = 0, ton = 0;
    if (edges.length >= 2) {
      var e0 = edges[0], e1 = edges[edges.length - 1];
      var period = (rec.t[e1] - rec.t[e0]) / (edges.length - 1);
      f = 1 / period;
      var onCount = 0;
      for (i = e0; i < e1; i++) onCount += rec.s[i];
      duty = onCount / (e1 - e0);
      ton = duty * period;
    } else {
      var on = 0; for (i = 0; i < n; i++) on += rec.s[i];
      duty = n ? on / n : 0;
    }
    var vmin = Infinity, vmax = -Infinity, vsum = 0, imin = Infinity, imax = -Infinity;
    for (i = 0; i < n; i++) {
      var v = rec.vo[i]; vsum += v; if (v < vmin) vmin = v; if (v > vmax) vmax = v;
      if (rec.il[i] < imin) imin = rec.il[i]; if (rec.il[i] > imax) imax = rec.il[i];
    }
    var vavg = vsum / n;
    var pout = acc.pout / acc.n, pin = acc.pin / acc.n;

    return {
      params: p, rec: rec, n: n, edges: edges, falls: falls,
      startup: strace, startupPeak: startupPeak, startupLimited: startupLimited, reachedAt: reachedAt,
      stats: {
        f: f, duty: duty, ton: ton, toff: f ? 1 / f - ton : 0,
        vavg: vavg, ripple: vmax - vmin, iavg: vavg / p.rload, ilmin: imin, ilmax: imax,
        dcm: imin <= 1e-6, pin: pin, pout: pout, eff: pin > 0 ? pout / pin : 0,
        pq1: acc.pq1 / acc.n, pd: acc.pd / acc.n, pl: acc.pl / acc.n, prz: acc.prz / acc.n,
        pdrive: acc.pdrive / acc.n,
        iin: pin / p.vin, zdrop: (p.vin + 0.4) * kc, toffMin: (p.vin + 0.4) * p.c2 / ((p.vin - p.vz) / p.rz),
        warnVebo: warnVebo, warnLimit: warnLimit, dropout: f === 0 && duty > 0.99
      }
    };
  }

  var api = { simulate: simulate, DEFAULTS: DEFAULTS };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.BlackSim = api;
})(this);

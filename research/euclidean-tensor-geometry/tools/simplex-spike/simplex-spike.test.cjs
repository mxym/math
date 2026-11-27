#!/usr/bin/env node
'use strict';
const {spawnSync}=require('node:child_process');
const assert=require('node:assert/strict');
const path=require('node:path');
const cli=path.join(__dirname,'simplex-spike.cjs');
const cases=[
 {
  name:'2-simplex facet',
  input:{lambda:['1/2','1/2',0],a:['1/2','1/2',-1]},
  expected:[2,1,true,2,'1','4',['4/3','4/3','-8/3'],'48','1']
 },
 {
  name:'2-simplex vertex, affine degeneracy',
  input:{lambda:[1,0,0],a:[3,-1,-2]},
  expected:[2,0,true,1,'3','3',['1','-1/3','-2/3'],'7','0']
 },
 {
  name:'3-simplex edge, order two with mixed nodes',
  input:{lambda:['1/2','1/2',0,0],a:[0,0,-1,1]},
  expected:[3,1,true,2,'1','2',['1/2','1/2','-5/4','1/4'],'17','1']
 },
 {
  name:'3-simplex vertex, mixed nodes with positive repeats',
  input:{lambda:[1,0,0,0],a:[1,-1,-1,1]},
  expected:[3,0,true,1,'2','5/4',['5/16','-7/32','-7/32','1/8'],'107/64','3/4']
 },
 {
  name:'4-simplex vertex, mixed nodes with zero repeats',
  input:{lambda:[1,0,0,0,0],a:[0,-1,1,0,0]},
  expected:[4,0,true,1,'1','1/2',['1/10','-3/20','1/20','0','0'],'7/16','1/2']
 },
 {
  name:'inward motion, zero polar loss',
  input:{lambda:[1,0,0,0],a:[-3,1,1,1]},
  expected:[3,0,false,1,'0','0',['0','0','0','0'],'0','0']
 }
];
function run(input) {
  const result=spawnSync(process.execPath,[cli],{input:JSON.stringify(input),encoding:'utf8'});
  if(result.error) throw result.error;
  return result;
}
for (const {name,input,expected} of cases) {
  const result=run(input);
  assert.equal(result.status,0,result.stderr);
  const got=JSON.parse(result.stdout);
  assert.deepEqual([got.dimension,got.faceDimension,got.spikeOutside,got.polarLossOrder,got.primalGainCoefficient,
   got.polarLossCoefficient,got.santaloShiftCoefficient,got.recenterGainCoefficient,got.optimizedProductLinearCoefficient],expected,name);
  assert.equal(got.recenterGainOrder,2*got.polarLossOrder,name);
  assert.equal(got.santaloShiftOrder,got.polarLossOrder,name);
  assert.equal(got.primalGainOrder,1,name);
}
for(const input of [
 {lambda:[1,0,0],a:[1.5,-1,-.5]},
 {lambda:['1/0',0],a:[1,-1]},
 {lambda:['1/2','1/2'],a:[1,-1]},
 {lambda:[1,0],a:[1,0]},
]) {
  const result=run(input);
  assert.equal(result.status,1);
  assert.match(result.stderr,/^simplex-spike:/);
  assert.equal(result.stdout,'');
}
console.log('PASS: '+cases.length+' exact CLI fixtures and 4 validation fixtures');

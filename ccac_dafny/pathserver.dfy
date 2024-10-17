include "buffer.dfy"



module PathServer {
    import opened Buffer
    const c := 5
    const slack := 2
    const loss_threshold := 10
    const delay := 2
function min(a: int, b: int): int
{ /* body must be an expression */
if a < b then a else b
}

function max(a: int, b: int): int
{ /* body must be an expression */
if a > b then a else b
}

  method gettokenamount(start: int, thresh: int, size: int ) returns (y : int) 
requires size >= 0
ensures y >= 0
ensures y <= size
ensures start + size >= thresh ==> y >= thresh - start
ensures start + size <= thresh ==> y == size
{
  var t :| 0 <= t <= size;
  if  (start + size <= thresh) {
    return size;
  }
  else if (start <= thresh) {
    var x :| 0 <= x <= start + size - thresh;
    return x + thresh - start;

  }
  return t;
}
predicate sorted(s: seq<int>)
{
    forall i :: 1 <= i < |s| ==> s[i] >= s[i-1]
}
predicate sorted2(s: seq<int>)
{
    forall i :: 1 <= i < |s| ==> (c * i) - s[i] >= c * (i - 1) - s[i-1]
}

predicate lessthanc(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] <= c * (i + 1)
}

predicate bothlessthanc(s1: seq<int>, s2: seq<int>)
{
    |s1| == |s2| && forall i :: 0 <= i < |s1| ==> s1[i] + s2[i] <= c * (i + 1)
}

predicate sameforn(s1: seq<int>, s2: seq<int>, n: int )
{
   |s1| >= n && |s2| >= n && forall i :: 0 <= i < n ==> s1[i] == s2[i]
}



predicate greaterthan0(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] >= 0
}


  method run_ts (ibs: array<Buf>, obs: array<Buf>, tokens: int, wastetrack: seq<int>, servicetrack: seq<int>, time: int)  returns (x : int, y : seq<int>, z  : seq<int>, recent_loss: int)
    requires ibs.Length >= 1
    requires obs.Length >= 3
    modifies ibs
    modifies obs
    requires |wastetrack| == time - 1
    requires |servicetrack| == time - 1
    requires time >= 1
    requires sorted(wastetrack)
    requires sorted2(wastetrack)
    requires lessthanc(wastetrack) 
    requires sorted(servicetrack)
    requires lessthanc(servicetrack)
    requires greaterthan0(servicetrack)
    requires greaterthan0(wastetrack)
    requires bothlessthanc(servicetrack, wastetrack)
    requires time == 1 ==> tokens == 0
    requires time > 1 ==> tokens == c * (time - 1) - wastetrack[time - 2] - servicetrack[time - 2]
    ensures sorted(y)
    ensures sorted(z)
    ensures lessthanc(z)
    ensures lessthanc(y)
    ensures sorted2(y)
    ensures greaterthan0(z)
    ensures greaterthan0(y)
    ensures bothlessthanc(y, z)
    ensures |y| == time
    ensures |z| == time
    ensures time > 1 ==> x == tokens + c - y[time - 1] + wastetrack[time - 2] - z[time - 1] + servicetrack[time - 2]
    ensures x == c * time - y[time - 1] - z[time - 1]
    ensures time > 1 ==> sameforn(wastetrack, y, time - 1)
    ensures time > 1 ==> sameforn(servicetrack, z, time - 1)
    ensures tokens + c <= backlog(ibs[0]) && time > 1 ==> y[time - 1] - y[time - 2] == 0
    ensures tokens + c <= backlog(ibs[0]) && time == 1 ==> y[time - 1] == 0
    ensures recent_loss >= 0
  {
    // obs[0] serviced, obs[1] loss, obs[2] ack
    var new_tokens := gettokenamount(tokens, backlog(ibs[0]), c);
    var waste_tokens := c - new_tokens;
    var lowerbound := 0;
    if (time >= delay) {
        lowerbound := max(0, c * (time - delay) - wastetrack[time - delay]);
    }
    var wasteadd := waste_tokens;
    if(|wastetrack| > 0) {
      wasteadd := wastetrack[|wastetrack| - 1] + waste_tokens;
    }
    var upperbound := (c * time) - wasteadd;
    var servicetotal :| lowerbound <= servicetotal <= upperbound;
    if (time > 1 && servicetotal <= servicetrack[|servicetrack| - 1]) {
      servicetotal := servicetrack[|servicetrack| - 1];
    }
    var prev_service := 0;
    if(time > 1) {
      prev_service := servicetrack[|servicetrack| - 1];
    }
    var serviceincr := servicetotal - prev_service;
    var arrival_buf := ibs[0];
    ghost var prev_backlog := |arrival_buf|;
    if(serviceincr <= servicetotal) {
    for j := 0 to serviceincr 
        invariant 0 <= j <= serviceincr
        invariant backlog(arrival_buf) >= 0
        invariant backlog(arrival_buf) >= prev_backlog - j - 1
        invariant |arrival_buf| == 0 ==> backlog(arrival_buf) <= prev_backlog 
        invariant |arrival_buf| > 0 ==> |arrival_buf| <= prev_backlog - j
    {
        ghost var prev_backlog := |arrival_buf|;
        var (ib, ob) := move(arrival_buf, obs[0]);
        arrival_buf := ib;
        obs[0] := ob;
        obs[2] := obs[2] + [time];
    }
    }
    ibs[0] := arrival_buf;
    var lost := 0;
    var newtokens := tokens + new_tokens - serviceincr;
    if(backlog(ibs[0]) - newtokens > loss_threshold) {
      var lost_bytes := (backlog(ibs[0]) - loss_threshold);
      ibs[0], obs[1] := moven(ibs[0], obs[1], lost_bytes);
      lost := lost_bytes;
    }
    return newtokens, 
    if time == 1 then [waste_tokens] else wastetrack + [wastetrack[|wastetrack| - 1] + waste_tokens], 
    if time == 1 then [servicetotal] else servicetrack + [servicetotal], lost;
  }


}
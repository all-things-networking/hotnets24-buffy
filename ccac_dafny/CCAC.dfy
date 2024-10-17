include "buffer.dfy"
include "pathserver.dfy"
include "CCA.dfy"
include "delayserver.dfy"
import CC = CCA
const T := 10
import opened Buffer
//method flush(ob: Buf, ib: Buf)
// method flush(ob: array<Buf>, oi: int, ib: array<Buf>, ii: int)

method Main(){
  var cca_ibs := new Buf[3];
  var cca_obs := new Buf[1];
  var path_ibs := new Buf[1];
  var path_obs := new Buf[3];
  var delay_ibs := new Buf[1];
  var delay_obs := new Buf[1];

  var cwnd := 10.0;
  var in_flight := 0;
  var wastetrack := [];
  var servicetrack := [];
  var tokens := 0;
  var time := 1;
  var sent := 0;
  var lost := 0;
  var seen_serviced := 0;

  for t := 1 to 100 
    invariant 1 <= t <= 101
    invariant backlog(cca_ibs[2]) >= t - 1 
    {
    cca_ibs[2] := cca_ibs[2] + [1];
  }
  assert(backlog(cca_ibs[2]) > 98);
  cca_obs[0] := [];
  cca_ibs[1] := [];
  cca_ibs[0] := [];
  for t := 1 to T
    invariant 1 <= t <= T
    invariant |wastetrack| == time - 1
    invariant |servicetrack| == time - 1
    invariant PathServer.sorted(wastetrack)
    invariant PathServer.sorted2(wastetrack)
    invariant PathServer.lessthanc(wastetrack)
    invariant PathServer.sorted(servicetrack)
    invariant PathServer.greaterthan0(servicetrack)
    invariant PathServer.greaterthan0(wastetrack)
    invariant PathServer.greaterthan0(wastetrack)
    invariant PathServer.bothlessthanc(wastetrack, servicetrack)
    invariant cwnd.Floor >= 0
    invariant |cca_ibs[2]| >= cwnd.Floor + 1
    invariant time == 1 ==> tokens == 0
    invariant time > 1 ==> tokens == PathServer.c * (time - 1) - wastetrack[time - 2] - servicetrack[time - 2]
    invariant |cca_obs[0]| == 0
    //invariant sent == lost + seen_serviced + |path_ibs[0]| + |delay_ibs[0]| + |cca_ibs[1]| + |iba[0]| 
    invariant lost >= 0
    invariant seen_serviced >= 0
    invariant sent >= 0
   {
    var a, b, c, d := CC.run_t(cca_ibs, cca_obs, cwnd, sent, lost, seen_serviced);
    assert(|cca_obs[0]| == b - sent);
    for i := 0 to (cwnd.Floor + 2)
      invariant 0 <= i <= cwnd.Floor + 2
      invariant |cca_ibs[2]| >= i  
      invariant |cca_obs[0]| == b - sent
    {
      cca_ibs[2] := cca_ibs[2] + [1];
    }
    assert(|cca_obs[0]| == b - sent);
    cwnd := a;
    sent := b;
    lost := c;
    seen_serviced := d;
    path_ibs[0] := path_ibs[0] + cca_obs[0];
    cca_obs[0] := [];
    print(path_ibs[0]);
    tokens, wastetrack, servicetrack := PathServer.run_ts(path_ibs, path_obs, tokens, wastetrack, servicetrack, time);
    cca_ibs[0] := cca_ibs[0] +  path_obs[1];
    path_obs[1] := [];
    delay_ibs[0] := delay_ibs[0] +  path_obs[2];
    path_obs[2] := [];
    print(delay_ibs[0]);
    DelayServer.run_t(delay_ibs, delay_obs, time);
    cca_ibs[1] := cca_ibs[1] + delay_obs[0];
    delay_obs[0] := [];
    time := time + 1;
    print(servicetrack);
    print(wastetrack);
    print(in_flight);
    print(in_flight);
    print("\n");
  }
  //print(path_ibs[0]);
  //print(cca_ibs[2]);
  //print(|cca_ibs[2]|);
}


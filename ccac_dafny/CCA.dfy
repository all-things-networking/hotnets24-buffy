include "buffer.dfy"


module CCA {
  import opened Buffer
method AIMD(recent_loss: int, cwnd: real) returns (y : real) 
  ensures 0 <= y.Floor <= cwnd.Floor + 1
  requires cwnd.Floor >= 0
{
  if (recent_loss > 0) {
    return cwnd / 2.0;
  }
  else {
    return cwnd + 0.3;
  }
}

method ArrivalTime(cwnd: real, in_flight: int) returns (y : int) 
ensures y >= 0
ensures y <= cwnd.Floor
requires cwnd.Floor >= 0
//requires in_flight >= 0
ensures in_flight < cwnd.Floor && in_flight >= 0 ==> in_flight + y == cwnd.Floor
{
  if(in_flight < 0) {
    return 0;
  }
  if(in_flight < cwnd.Floor) {
    return cwnd.Floor - in_flight;
  }
  return 0;
}

  method run_t (ibs: array<Buf>, obs: array<Buf>, cwnd: real, total_sent: int, 
  total_lost: int, total_seen_serviced: int, recent_loss: int) returns (cwnd' : real, total_sent_new : int, total_lost_new : int, total_seen_serviced_new : int) 
    requires total_lost >= 0 && total_seen_serviced >= 0
    requires recent_loss >= 0
    requires ibs.Length >= 3
    requires obs.Length >= 1
    requires backlog(obs[0]) == 0
    requires |ibs[2]| >= cwnd.Floor + 1
    //requires total_sent >= total_lost + total_seen_serviced + |ibs[0]| + |ibs[1]|
    modifies ibs
    modifies obs
    requires cwnd.Floor >= 0
    ensures cwnd'.Floor >= 0
    ensures cwnd'.Floor <= cwnd.Floor + 1
    requires total_sent >= 0
    //ensures  y.Floor <= a - b - c
    ensures total_sent_new - total_sent == backlog(obs[0])
    ensures total_lost_new >= 0
    ensures total_seen_serviced_new >= 0
{
    //ibs[0] is loss, ibs[1] is serviced,ibs[2] is input obs[0] is arrived, 
    var in_flight := total_sent - total_lost - total_seen_serviced;
    // var recent_loss := backlog(ibs[0]);
    // ibs[0] := [];
    total_lost_new := total_lost + recent_loss;

    var recent_service := backlog(ibs[1]);
    ibs[1] := [];
    total_seen_serviced_new := total_seen_serviced + recent_service;

    cwnd' := AIMD(recent_loss, cwnd);

    assert(|ibs[2]| >= cwnd'.Floor);

    in_flight := total_sent - total_seen_serviced_new - total_lost_new;

    var arrive_amount := ArrivalTime(cwnd', in_flight);
    // assert(in_flight >= 0);
    assert(in_flight >= 0 && in_flight < cwnd'.Floor ==> in_flight + arrive_amount == cwnd'.Floor);
    in_flight := in_flight + arrive_amount;
    ibs[2], obs[0] := moven(ibs[2], obs[0], arrive_amount);
    total_sent_new := total_sent + arrive_amount;
  }
}
module queue

import std/os/env
import std/num/random
import std/num/int32

pub alias rndstate = sfc
alias rndres = sfc-result

fun rnd-step( r : rndstate ) : rndres
  sfc-step(r)

fun rnd-init( s0 : int, s1 : int ) : rndstate
  (sfc-init32(s0.int32,s1.int32))

pub value struct queueI<q>
  qempty : q
  qsnoc : (q,int) -> pure q
  quncons : q -> pure maybe2<int,q>

fun bench-snoc( i : int32, qi : queueI<q>, rs : rndstate, queue : q ) : pure q
  if i > 0.int32 then
    val step = rnd-step(rs)
    val q' = qi.qsnoc.(queue, step.rnd.int)
    bench-snoc(i - 1.int32, qi, step.rstate, q')
  else queue

fun bench-uncons( i : int32, queue : q, qi : queueI<q>, acc = 0.int32 ) : pure int32
  if i > 0.int32 then
    match qi.quncons.(queue)
      Just2( x, q ) -> bench-uncons(i - 1.int32, q, qi, acc + i*x.int32)
      Nothing2 -> throw("uncons failed")
  else acc

fun bench-unconsn( i : int32, n : int32, queue : q, qi : queueI<q>, acc = 0.int32 ) : pure int32
  if n > 1.int32 then
    val acc' = bench-uncons(i, queue, qi, acc)
    bench-unconsn(i, n - 1.int32, queue, qi, acc')
  elif n == 1.int32 then
    bench-uncons(i, queue, qi, acc)
  else acc

pub fun bench( ops : int32, n : int32, qi : queueI<q> ) : pure int32
  val q = bench-snoc( ops, qi, rnd-init(42,43), qi.qempty)
  bench-unconsn( ops / n, n, q, qi )

pub fun benchmain( qi : queueI<q>, ops : int = 5000000) : io ()
  val n = get-args().head("").parse-int.default(1).int32
  // val ops = 5000000.int32
  val sum = bench(ops.int32, n, qi)
  println("Checksum: " ++ show(sum))
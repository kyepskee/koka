import queue

lazy type stream<a>
  SNil
  SCons( head : a, tail : stream<a> )
  lazy SAppRev( pre : stream<a>, post : list<a> ) ->
    match pre
      SNil        -> sreverse(post)
      SCons(x,xx) -> SCons(x,SAppRev(xx,post))

fip fun sreverse-acc( xs : list<a>, acc : stream<a> ) : stream<a>
  match xs
    Cons(x,xx) -> sreverse-acc(xx, SCons(x,acc))
    Nil        -> acc

fip fun sreverse( xs : list<a> ) : stream<a>
  sreverse-acc(xs,SNil)

pub fbip fun stream/list( s : stream<a> ) : div list<a>
  match s
    SCons(x,xx) -> Cons(x,xx.list)
    SNil -> Nil

fun stream(start : int, end : int)
  if (start>end) then SNil else SCons(start,stream(start+1,end))

pub fun test1()
  SAppRev(stream(1,3),[6,5,4]).list.println

/*
// this should be generated; `lazy-update(s,...)`` is always inserted at tail-position.
// If the argument is not a syntactic non-lazy constructor a recursive call to `stream-eval` is added as well. (case `(A)`)
// If the argument is a singleton (`SNil`), larger, or unknown (`sreverse(post)`),
// an indirection is automatically inserted (`SIndirect`). The latter two issue a warning.
noinline fbip fun stream-eval( s : stream<a> ) : _ stream<a>
  lazy-whnf-target(s)
  lazy match s
    SAppRev( pre, post )
      -> lazy match stream-forcex(pre)
           SNil        -> lazy-update(s,stream-eval(sreverse(post)))  // (A)
           SNil        -> match post
                            Cons(x,xx) -> lazy-update(s,SCons(x,sreverse(xx)))
                            Nil        -> lazy-update(s,SNil)
           SCons(x,xx) -> lazy-update(s,SCons(x,SAppRev(xx,post)))
           _           -> lazy-update(s,SNil) // this cannot happen; todo: fix partial check
    // generated
    SIndirect(ind)
      -> ind // or stream-eval(ind) ?
    _ -> s

noinline fbip fun stream-whnf( s : stream<a> ) : div stream<a>
  if kk-datatype-ptr-is-unique(s) || !lazy-atomic-enter(s,stream/lazy-tag) then
    stream-eval(s)
  else
    val v = stream-eval(s)
    lazy-atomic-leave(s)
    v

fbip fun stream-forcex( s : stream<a> ) : div stream<a>
  // stream-eval(s)
  if kk-datatype-is-whnf(s,stream/lazy-tag) then s else stream-whnf(s)

inline fbip fun stream-force( s : stream<a> ) : div stream<a>
  // stream-eval(s)
  if kk-datatype-is-whnf(s,stream/lazy-tag) then s else stream-whnf(s)
*/


struct bqueue<a>
  front : stream<a>
  front-len : int
  rear : list<a>
  rear-len : int

val bankers/empty = Bqueue( SNil, 0, Nil, 0 )

fun is-empty( ^q : bqueue<a> ) : bool
  q.front-len==0

fun size( ^q : bqueue<a> ) : int
  q.front-len + q.rear-len


fip(1) fun check( q : bqueue<a> ) : bqueue<a>
  match q
    Bqueue(front, front-len, rear, rear-len) ->
      if (front-len >= rear-len)
       then Bqueue(front, front-len, rear, rear-len)
       else Bqueue( SAppRev(front,rear), front-len + rear-len, Nil, 0)

fip(2) fun snoc( q : bqueue<a>, x : a ) : bqueue<a>
  match q
    Bqueue(front,front-len,rear,rear-len) ->
      Bqueue(front, front-len, Cons(x,rear), rear-len+1).check

fbip(2) fun uncons( Bqueue(front,front-len,rear,rear-len) : bqueue<a> ) : div maybe2<a,bqueue<a>>
  match front
    SCons(x,xx) -> Just2(x, Bqueue(xx,front-len - 1,rear,rear-len).check)
    SNil        -> Nothing2

pub fun main()
  benchmain(QueueI(bankers/empty, snoc, uncons))

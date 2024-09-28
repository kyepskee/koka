import queue
import std/core/undiv

// internal: marker for lazy values that get matched to evaluate to whnf
inline fip extern lazy-whnf-target(target : a) : ()
  ""

// internal: explicitly force update-in-place for lazy values
fip extern lazy-update(target : a, x : a) : a
  c inline "#1"

// internal: test if a lazy value is in whnf
inline fip extern kk-datatype-is-whnf(^x:a, lazy-tag:int32) : bool
  c "kk_datatype_is_whnf"

inline fip extern kk-datatype-ptr-is-whnf(^x:a, lazy-tag:int32) : bool
  c "kk_datatype_ptr_is_whnf"


// internal: evaluate atomically (or return `false` if already evaluated)
inline fip extern lazy-atomic-enter(^target : a, lazy-tag: int32 ) : bool
  c "kk_lazy_atomic_enter"

// internal: release an atomically evaluated value
inline fip extern lazy-atomic-unblock(target : a) : ()
  c "kk_lazy_atomic_unblock"

// internal: is a lazy datatype thread shared?
inline fip extern kk-datatype-ptr-is-thread-shared(^x : a) : bool
  c "kk_datatype_ptr_is_thread_shared"


type stream<a>
  SNil
  SCons( head : a, tail : stream<a> )
  SIndirect( s : stream<a> )
  lazy SAppRev( pre : stream<a>, post : list<a> ) ->
    match pre
      // SNil        -> stream-eval(lazy-update(s,sreverse(post)))  // (A)
      SNil        -> match post
                      Cons(x,xx) -> SCons(x,SNil) // sreverse(xx))
                      Nil        -> SNil
      SCons(x,xx) -> SCons(x,SAppRev(xx,post))
      _           -> SNil // cannot happen, fix

fip fun sreverse-acc( xs : list<a>, acc : stream<a> ) : stream<a>
  match xs
    Cons(x,xx) -> sreverse-acc(xx, SCons(x,acc))
    Nil        -> acc

fip fun sreverse( xs : list<a> ) : stream<a>
  sreverse-acc(xs,SNil)




// this should be generated; `lazy-update(s,...)`` is always inserted at tail-position.
// If the argument is not a syntactic non-lazy constructor a recursive call to `stream-eval` is added as well. (case `(A)`)
// If the argument is a singleton (`SNil`), larger, or unknown (`sreverse(post)`),
// an indirection is automatically inserted (`SIndirect`). The latter two issue a warning.
noinline fbip fun stream-eval( s : stream<a> ) : _ stream<a>
  lazy-whnf-target(s)
  match s
    SAppRev( pre, post )
      -> match stream-forcex(pre)
           // SNil        -> stream-eval(lazy-update(s,sreverse(post)))  // (A)
           SNil        -> match post
                            Cons(x,xx) -> lazy-update(s,SCons(x,sreverse(xx)))
                            Nil        -> lazy-update(s,SNil)
           SCons(x,xx) -> lazy-update(s,SCons(x,SAppRev(xx,post)))
           _           -> lazy-update(s,SNil) // this cannot happen; todo: fix partial check
    // generated
    SIndirect(ind)
      -> stream-eval(pretend-decreasing(ind))
    _ -> s

noinline fbip fun stream-whnf( s : stream<a> ) : div stream<a>
  // force(s,stream/lazy-tag,stream-eval)
  if kk-datatype-ptr-is-thread-shared(s) && lazy-atomic-enter(s,stream/lazy-tag) then
    val v = stream-eval(s)
    lazy-atomic-unblock(s)
    v
  else
    stream-eval(s)

fbip fun stream-forcex( s : stream<a> ) : div stream<a>
  // stream-eval(s)
  if kk-datatype-is-whnf(s,stream/lazy-tag) then s else stream-whnf(s)




inline fbip fun stream-force( s : stream<a> ) : div stream<a>
  // stream-eval(s)
  if kk-datatype-is-whnf(s,stream/lazy-tag) then s else stream-whnf(s)


pub fbip fun stream/list( s : stream<a> ) : div list<a>
  match stream-force(s)
    SCons(x,xx) -> Cons(x,xx.list)
    SNil -> Nil
    _    -> Nil // cannot happen

/*
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
  match stream-force(front)
    SCons(x,xx) -> Just2(x, Bqueue(xx,front-len - 1,rear,rear-len).check)
    SNil        -> Nothing2
    _           -> Nothing2 // todo: fix partial check

pub fun main()
  benchmain(Queue(bankers/empty, snoc, uncons))
*/
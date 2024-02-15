## Note: this is for the JS backend only!
## It is a compatibility layer, which simulates the interface of arraymancer tensors
## which we actually use in datamancer
import std / sequtils
import math
export math
import stats
export stats

type
  Tensor*[T] = seq[T]

proc newTensor*[T](n: int): Tensor[T] = Tensor[T](newSeq[T](n))
proc newTensorWith*[T](n: int, val: T): Tensor[T] = Tensor[T](newSeqWith(n, val))
proc newTensorUninit*[T](n: int): Tensor[T] = newTensor[T](n)
#proc `[]=`*[T](t: var Tensor[T], idx: int, val: T) =
#  t[idx] = val
proc `[]=`*[T](t: var Tensor[T], idxs: HSlice[int, int], val: T) =
  for a in idxs:
    t[a] = val

proc toTensor*[T](x: openArray[T]): Tensor[T] = Tensor[T](@x)
proc toSeq1D*[T](x: Tensor[T]): seq[T] =
  result = newSeq[T](x.len)
  for i, el in x:
    result[i] = el
proc clone*[T](t: Tensor[T]): Tensor[T] = t
proc size*[T](t: Tensor[T]): int = t.len
proc astype*[T; U](t: Tensor[T], dtype: typedesc[U]): Tensor[U] = t.mapIt(it.dtype)
proc map*[T; U](t: Tensor[T], fn: proc(x: T): U): Tensor[U] = t.mapIt(fn(it))
template map_inline*(t: untyped, body: untyped): untyped =
  type U = typeof(block:
                    let x {.inject.} = t[0]
                    let tmp = body
                    tmp)

  var res = newTensor[U](t.len)
  var i = 0
  for x {.inject.} in t:
    res[i] = body
    inc i
  res

template apply2_inline*(t1, t2: untyped, body: untyped): untyped =
  type U = typeof(block:
                    let x {.inject.} = t1[0]
                    let y {.inject.} = t2[0]
                    let tmp = body
                    tmp)

  doAssert t1.len == t2.len
  for i in 0 ..< t1.len:
    let x {.inject.} = t1[i]
    let y {.inject.} = t2[i]
    t1[i] = body

import seqmath, math
proc concat*[T](ts: varargs[Tensor[T]], axis: int = 0): Tensor[T] = Tensor[T](concat(ts))

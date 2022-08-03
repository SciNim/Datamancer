import tables, sets
import column, value

type
  DataFrameKind* = enum
    dfNormal, dfGrouped

  # where value is as usual
  # then
  DataTable*[T] = ref object
    len*: int
    data*: OrderedTable[string, T] ## `T` is the column kind
    case kind*: DataFrameKind
    of dfGrouped:
      # a grouped data frame stores the keys of the groups and maps them to
      # a set of the categories
      groupMap*: OrderedTable[string, HashSet[Value]]
    else: discard

  DataFrame* = DataTable[Column]

  DataFrameLike* = concept x
    x.len is int
    x.data[string].kind is ColKind
    x.kind is DataFrameKind

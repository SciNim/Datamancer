# Simple H5 serialization of data frames and tensors

from std / os import `/`, extractFilename
from std / strutils import replace
import nimhdf5
import ./dataframe, ./column

proc toH5*[T](h5f: H5File, x: Tensor[T], name = "", path = "/") =
  ## Stores the given arraymancer `Tensor` in the given H5 file using the
  ## shape info to construct an equivalent dataset.
  let dset = h5f.create_dataset(path / name,
                                @(x.shape), # 1D, so use length
                                T,
                                overwrite = true)
  if x.size > 0:
    when T is KnownSupportsCopyMem:
      dset.unsafeWrite(x.toUnsafeView(), x.size.int)
    else:
      dset[dset.all] = x.toSeq1D

proc toH5*(h5f: H5File, x: DataFrame, name = "", path = "/") =
  ## Stores the given datamancer `DataFrame` as in the H5 file.
  ## This is done by constructing a group for the dataframe and then adding
  ## each column as a 1D dataset.
  ##
  ## Alternatively we could also store it as a composite datatype, but that is less
  ## efficient for reading individual columns.
  let grp = path / name
  echo "Generating group ", grp
  discard h5f.create_group(grp)
  if x == nil: return # nothing to serialize!
  for k in getKeys(x):
    withNativeTensor(x[k], val):
      when typeof(val) isnot Tensor[Value]:
        h5f.toH5(val, k.replace("/", "|"), grp)
      else:
        echo "[WARNING]: writing object column " & $k & " as string values!"
        h5f.toH5(val.valueTo(string), k.replace("/", "|"), grp)

proc fromH5*(h5f: H5File, res: var DataFrame, name = "", path = "/", exclude: seq[string] = @[]) =
  ## Stores the given datamancer `DataFrame` as in the H5 file.
  ## This is done by constructing a group for the dataframe and then adding
  ## each column as a 1D dataset.
  ##
  ## Alternatively we could also store it as a composite datatype, but that is less
  ## efficient for reading individual columns.
  let grp = h5f[(path / name).grp_str]
  for dataset in items(grp):
    let col = dataset.name.extractFilename()
    if col notin exclude:
      withDset(dataset):
        res[col] = dset

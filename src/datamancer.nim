## .. include:: ./docs/datamancer.rst

when not defined(js):
  import datamancer / [dataframe, io]
  export dataframe, io
else:
  import datamancer / [dataframe, io]
  export dataframe, io

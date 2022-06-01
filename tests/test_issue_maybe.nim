import datamancer
let df = seqsToDf({"x": @[1, 2, 3, 4, 5], "y": @[5, 10, 15, 20, 25]})
try:
  echo df.mutate(f{float: "ratio" ~ `x`/sum(`x`)}).summarize(f{float: mean(`field_that_does_not_exist`)})
except KeyError:
  continue # we expect a KeyError. Do we get an AssertionError on some platforms / nim versions?

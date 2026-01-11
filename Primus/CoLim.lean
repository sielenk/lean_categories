import Primus.Category
import Primus.CoCone


def CoLim{JJ CC: Cat}(F: Fun JJ CC) :=
  InitialObject (coConeCat F)

import Primus.Core.Category
import Primus.Limits.CoCone


abbrev CoLim{JJ CC: Cat}(F: Fun JJ CC) :=
  InitialObject (coConeCat F)

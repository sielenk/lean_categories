import Primus.Core.Category
import Primus.Limits.Cone


abbrev Lim{JJ CC: Cat}(F: Fun JJ CC) :=
  TerminalObject (coneCat F)

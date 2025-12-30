import Primus.Category
import Primus.Cone


def Lim{JJ CC: Cat}(F: Fun JJ CC) :=
  TerminalObject (coneCat F)

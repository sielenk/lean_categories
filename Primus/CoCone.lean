import Primus.Category
import Primus.Functor
import Primus.Opposite
import Primus.Cone


def coConeCat{JJ CC: Cat}(F: Fun JJ CC): Cat :=
  op (coneCat F)

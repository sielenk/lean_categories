import Primus.Category
import Primus.Functor
import Primus.Opposite
import Primus.Cone


variable {JJ CC: Cat}
variable (F: Fun JJ CC)

def coConeCat: Cat := op (coneCat F)

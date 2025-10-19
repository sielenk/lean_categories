import Primus.Category
import Primus.Functor
import Primus.Opposite
import Primus.Cone


variable {JJ CC: category}
variable (F: functor JJ CC)

def coConeCat: category := op (coneCat F)

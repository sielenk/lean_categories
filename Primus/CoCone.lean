import Primus.Category
import Primus.Functor
import Primus.Opposite
import Primus.Cone


variable {JJ CC: Category}
variable (F: functor JJ CC)

def coConeCat: Category := op (coneCat F)

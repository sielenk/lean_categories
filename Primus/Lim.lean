import Primus.Category
import Primus.Cone

variable {JJ CC: category}
variable (F: functor JJ CC)

def lim := terminalObject (coneCat F)

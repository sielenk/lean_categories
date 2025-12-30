import Primus.Category
import Primus.Cone

variable {JJ CC: Category}
variable (F: functor JJ CC)

def lim := terminalObject (coneCat F)

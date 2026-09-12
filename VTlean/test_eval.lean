import VTlean.Dream
open B

#eval Fintype.card (List.Vector B 5)

-- Try to synthesize it and print the term
def instF : Fintype (List.Vector B 5) := inferInstance
#print instF

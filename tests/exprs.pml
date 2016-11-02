def unit : ο = {}
def null : ο = []
def triv : ο = {} ⇒ []
def blop = ∀ (x : ο) x
def id = λx.x
def stack = (λx.x) . ε
def delta = λx.x x
def omega : τ = delta delta
def arrow (a : ο) (b : ο) : ο = a ⇒ b

def test1 : τ =
  case C[{}] of
  | C[z] → z
  | D[w] → C[w]

def test2 : τ =
  case (λx.x) C[{}] of
  | C[z] → z
  | D[w] → C[w]

def fixid : τ = fix (λx.x)

def lamb_v : ι = Λ (a:ο) λx.x

def lamb_t : τ = Λ (a:ο) λx.x
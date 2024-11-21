import Mathlib.Tactic

/- An effort to build groups from scratch-/

/- There was a lot of flailing around to get it to accept normal way of writing multiplication, inverses and identity elements, and
I did not get it to work with the identity element.
-/

set_option quotPrecheck false


variable {myGroup: Type}
variable {I: myGroup }
variable {mul:myGroup→ myGroup→ myGroup}
variable {inv:myGroup → myGroup }



axiom axassoc: ∀ (g h k:myGroup),(mul g (mul h k)) = (mul (mul g h) k)
axiom axinv : ∀ (g: myGroup), (mul g (inv g)) = I ∧ (mul (inv g) g) = I
axiom axid :∀ (g: myGroup), mul g I=g  ∧ mul I g = g

#check axinv
postfix:max  "⁻¹" =>  inv
infixl:100  " * "  => mul
/-notation " I " => one   not sure how to make it be 1-/

/- Just to see how the notational stuff is working -/
example  {b:myGroup}:mul b (inv b) = I :=   by apply And.left (axinv b)
example {b: myGroup} : mul b (b⁻¹) = I := by apply And.left (axinv b)
example {b: myGroup} : b * b⁻¹ = I := by apply And.left (axinv b)
example {b: myGroup} : b * b⁻¹ = I := by apply And.left (axinv b)


example {a b c:myGroup}:   (mul a (mul b c))=(mul (mul a b) c)   :=  by apply axassoc a b c

/- Now a real theorem.  The identity is unique; there's
both a left and right version.  The first says there's a unique
left identity. -/

theorem unique_id_left (z: myGroup)(h : ∀ (g:myGroup),z*g = g):z = I := by
have h₁: z*I = z  :=  (And.left (axid z))
have h₁₁: z = z* I := Eq.symm h₁
have h₂: z * I = I := h I
exact Eq.trans h₁₁ h₂

/-Can't we do this with a calculational proof? We can! -/

theorem unique_id_left2 (z: myGroup)(h : ∀ (g:myGroup),z*g = g):z = I := by
calc
z = z * I := Eq.symm (And.left (axid z))
_ = I := h I

/-! Problems from the chapter on groups in Herstein's  _Topics in Algebra_,
both the theorems in the chapter text and exercises.-/

/- unique right identity -/
theorem unique_id_right (z: myGroup)(h : ∀ (g:myGroup),g * z = g):z = I := by
calc
z = I * z := Eq.symm (And.right (axid z))
_   = I := h I

/-unique left inverse -/



theorem unique_left_inverse (a b :myGroup)(h: b * a = I): b = a⁻¹ := by
have ha: I = a * a⁻¹  := Eq.symm (And.left (axinv a))
calc
b = b * I := Eq.symm (And.left (axid b))
_ = b * (a * a⁻¹):= by rw [ha]
_ = (b * a) * a⁻¹ :=  (axassoc b a a⁻¹)
_ = I * a⁻¹ := by rw [h]
_ = a⁻¹ := And.right (axid a⁻¹)

import Mathlib.Tactic

/- An effort to build groups from scratch-/

/- There was a lot of flailing around to get it to accept normal way of writing multiplication, inverses and identity elements, and
I did not get it to work with the identity element.
-/

set_option quotPrecheck false

axiom MyGroup:Type

axiom mul : MyGroup → MyGroup → MyGroup
axiom I : MyGroup
axiom inv: MyGroup → MyGroup

axiom axassoc: ∀ (g h k: MyGroup), (mul g (mul h k)) = (mul (mul g h) k) ∧ (mul (mul g h) k) = (mul g (mul h k))
axiom axinv (a : MyGroup): (mul a (inv a) = I) ∧ (mul (inv a) a = I)
axiom axid (a : MyGroup): (mul a I  = a) ∧ (mul I a = a)

#check axinv
postfix:max  "⁻¹" =>  inv
infixl:100  " * "  => mul
/-notation " I " => one   not sure how to make it be 1-/

/- Just to see how the notational stuff is working -/
example  {b: MyGroup} : mul b (inv b) = I := by apply And.left (axinv b)
example {b: MyGroup} : mul b (b⁻¹) = I := by apply And.left (axinv b)
example {b: MyGroup} : b * b⁻¹ = I := by apply And.left (axinv b)
example {b: MyGroup} : b * b⁻¹ = I := by apply And.left (axinv b)


example {a b c: MyGroup}: (mul a (mul b c))=(mul (mul a b) c) :=  by apply And.left (axassoc a b c)

/- Now a real theorem.  The identity is unique; there's
both a left and right version.  The first says there's a unique
left identity. -/

theorem unique_id_left (z: MyGroup)(h : ∀ (g: MyGroup), z*g = g):z = I := by
have h₁: z*I = z  :=  (And.left (axid z))
have h₁₁: z = z* I := Eq.symm h₁
have h₂: z * I = I := h I
exact Eq.trans h₁₁ h₂

/-Can't we do this with a calculational proof? We can! -/

theorem unique_id_left2 (z: MyGroup)(h : ∀ (g: MyGroup), z*g = g):z = I := by
calc
z = z * I := Eq.symm (And.left (axid z))
_ = I := h I

/-! Problems from the chapter on groups in Herstein's  _Topics in Algebra_,
both the theorems in the chapter text and exercises.-/

/- unique right identity -/
theorem unique_id_right (z: MyGroup)(h : ∀ (g: MyGroup), g * z = g): z = I := by
calc
z = I * z := Eq.symm (And.right (axid z))
_   = I := h I

/-unique left inverse -/

theorem unique_left_inverse (a b: MyGroup)(h: b * a = I): b = a⁻¹ := by
have ha: I = a * a⁻¹  := Eq.symm (And.left (axinv a))
calc
b = b * I := Eq.symm (And.left (axid b))
_ = b * (a * a⁻¹):= by rw [ha]
_ = (b * a) * a⁻¹ :=  And.left (axassoc b a a⁻¹)
_ = I * a⁻¹ := by rw [h]
_ = a⁻¹ := And.right (axid a⁻¹)

theorem inverse_inverse (a: MyGroup) : inv (inv a) = a := by
  have h₁: mul a (inv a) = I  := And.left (axinv a)
  have h₂: a = inv (inv a) := (unique_left_inverse (inv a) a h₁)
  exact Eq.symm (h₂)

theorem inv_mul (a b : MyGroup) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h₁ : (b⁻¹ * a⁻¹) * (a * b) = I := by
    have h₂ : (b⁻¹ * a⁻¹) * (a * b) = b⁻¹ * (a⁻¹ * (a * b)) := And.right (axassoc b⁻¹ a⁻¹ (a * b))
    have h₃ : a⁻¹ * (a * b) = (a⁻¹ * a) * b := And.left (axassoc a⁻¹ a b)
    rw [h₃] at h₂
    have h₄ : a⁻¹ * a = I := And.right (axinv a)
    rw [h₄] at h₂
    have h₅ : I * b = b := And.right (axid b)
    rw [h₅] at h₂
    have h₆ : b⁻¹ * b = I := And.right (axinv b)
    rw [h₆] at h₂
    exact h₂
  exact Eq.symm (unique_left_inverse (a * b) (b⁻¹ * a⁻¹) h₁)

theorem left_cancellation (a u w: MyGroup) : mul a u = mul a w → u = w := by
  intro h
  have h₁: inv a * (a * u) = inv a * (a * w) := by
    rw[h]
  have h₂: inv a * (a * u) = (inv a * a) * u := And.left (axassoc (inv a) a u)
  rw [h₂] at h₁
  have h₃: inv a * (a * w) = (inv a * a) * w := And.left (axassoc (inv a) a w)
  rw [h₃] at h₁
  have h₄: inv a * a = I := And.right (axinv a)
  rw [h₄] at h₁
  have h₅: I * u = u := And.right (axid u)
  rw [h₅] at h₁
  have h₆: I * w = w := And.right (axid w)
  rw [h₆] at h₁
  exact h₁

theorem right_cancellation (a u w : MyGroup): mul u a = mul w a → u = w := by
  intro h
  have h₁: (u * a) * inv a = (w * a) * inv a := by
    rw[h]
  have h₂: (u * a) * inv a = u * (a * inv a) := And.right (axassoc u a (inv a))
  rw [h₂] at h₁
  have h₃: (w * a) * inv a = w * (a * inv a) := And.right (axassoc w a (inv a))
  rw [h₃] at h₁
  have h₄: a * inv a = I := And.left (axinv a)
  rw [h₄] at h₁
  have h₅: u * I = u := And.left (axid u)
  rw [h₅] at h₁
  have h₆: w * I = w := And.left (axid w)
  rw [h₆] at h₁
  exact h₁

noncomputable def pow (a : MyGroup)(n : ℕ ): MyGroup :=
match n with
  |0 => I
  |n + 1 => a * (pow a n)

notation a " ^ " n => pow a n

theorem questionTwo (n : ℕ) (a b : MyGroup)  (h : ∀ x y : MyGroup, mul x y = mul y x) :
  pow (mul a b) n = mul (pow a n) (pow b n) := by
  induction n with
  | zero =>
    -- Base case: n = 0
    have h₁: pow (mul a b) 0 = I := rfl
    have h₂: I = mul I I := Eq.symm (And.left (axid I))
    rw [h₂] at h₁
    have h₃: mul I I = mul (pow a 0) (pow b 0) := rfl
    rw [h₃] at h₁
    exact h₁
  | succ n ih =>
    -- Inductive step: Assume the statement holds for n, prove for n + 1
    have h₁ : pow (mul a b) (n + 1) = mul (mul a b) (pow (mul a b) n) := rfl
    have h₂ : pow (mul a b) n =  (mul (pow a n) (pow b n)) := ih
    rw [h₂] at h₁
    have h₃ : mul (mul a b) (mul (pow a n) (pow b n)) = mul (mul (mul a b) (pow a n)) (pow b n) := And.left (axassoc (mul a b) (pow a n) (pow b n))
    rw [h₃] at h₁
    have h₄ : mul (mul a b) (pow a n) = mul a (mul b (pow a n)) := And.right (axassoc a b (pow a n))
    rw [h₄] at h₁
    have h₅ : mul b (pow a n) = mul (pow a n) b := h b (pow a n)
    rw [h₅] at h₁
    have h₆ : mul a (mul (pow a n) b) = mul (mul a (pow a n)) b := And.left (axassoc a (pow a n) b)
    rw [h₆] at h₁
    have h₇ : mul a (pow a n) = pow a (n+1) := rfl
    rw [h₇] at h₁
    have h₈ : mul (mul (pow a (n + 1)) b) (pow b n) = mul (pow a (n + 1)) (mul b (pow b n)) := And.right (axassoc (pow a (n + 1)) b (pow b n))
    rw [h₈] at h₁
    have h₉ : mul b (pow b n) = pow b (n + 1) := rfl
    rw[h₉] at h₁
    exact h₁

theorem questionThree (a b : MyGroup) (h : (pow a 2) * (pow b 2) = pow (a * b) 2) : a * b = b * a := by
  have h₁ : pow (a * b) 2 = pow a 2 * pow b 2 := Eq.symm h
  have h₂ : pow (a * b) 2 = (a * b) * (a * b) := by
    rw [pow]    -- (a*b)^2 = (a*b)*pow(a*b)1
    rw [pow]    -- (a*b)*pow(a*b)1 = (a*b)*((a*b)*pow(a*b)0)
    rw [pow]    -- (a*b)*((a*b)*pow(a*b)0) = (a*b)*((a*b)*I)
    have hx : (a * b) * ((a * b) * I) = ((a * b) * (a * b)) * I := And.left (axassoc (a * b) (a * b) I)
    rw [hx]
    rw [And.left (axid ((a * b) * (a * b)))]  -- ((a*b)*(a*b))*I = (a*b)*(a*b)
  rw [h₂] at h₁
  have h₃ : (a * b) * (a * b) = a * (b * (a * b)) := And.right (axassoc a b (a * b))
  rw [h₃] at h₁
  -- Prove (a ^ 2) * (b ^ 2) = (a * a) * (b * b)
  have h₄a : pow a 2 = a * a := by
    rw [pow]         -- (a^2) = a * (a^1)
    rw [pow]         -- (a^1) = a * (a^0)
    rw [pow]         -- (a^0) = I
    have ha : a * (a * I) = (a * a) * I := And.left (axassoc a a I)
    rw [ha]
    rw [And.left (axid (a * a))]  -- ((a*a)*I) = a*a
  have h₄b : pow b 2 = b * b := by
    rw [pow]         -- (b^2) = b * (b^1)
    rw [pow]         -- (b^1) = b * (b^0)
    rw [pow]         -- (b^0) = I
    have hb : b * (b * I) = (b * b) * I := And.left (axassoc b b I)
    rw [hb]
    rw [And.left (axid (b * b))]  -- ((b*b)*I) = b*b
  have h₄' : pow a 2 * pow b 2 = (a * a) * (b * b) := by
    rw [h₄a]
    rw [h₄b]
  rw [h₄'] at h₁
  have h₅ : (a * a) * (b * b) = a * (a * (b * b)) := And.right (axassoc a a (b * b))
  rw [h₅] at h₁
  have h₆ : b * (a * b) = a * (b * b) := (left_cancellation a (b * (a * b)) (a * (b * b))) h₁
  have h₇ : b * (a * b) = (b * a) * b := And.left (axassoc b a b)
  rw [h₇] at h₆
  have h₈ : a * (b * b) = (a * b) * b := And.left (axassoc a b b)
  rw [h₈] at h₆
  have h₉ : (b * a) = (a * b) := (right_cancellation b (b * a) (a * b)) h₆
  exact Eq.symm h₉



def mulclosed (H : MyGroup → Prop) := ∀ g h :MyGroup, H g ∧ H h → H (mul g h)

def invclosed (H: MyGroup → Prop ) := ∀ g : MyGroup, H g → H (inv g)

def subgroup (H : MyGroup→ Prop) := (mulclosed H) ∧ (invclosed H) ∧ (H I)

/- definition of coset
We write coset H K to mean H is a subgroup
and K is a coset (right? left?) of H -/

def coset (H K: MyGroup→ Prop)  : Prop :=
(subgroup H) ∧
(∃ g : MyGroup, ∀ x: MyGroup, K x ↔ (∃ h, (H h) ∧ x = mul h  g))

theorem right_coset_equality
  (H K₁ K₂ : MyGroup → Prop)
  (subH : subgroup H)
  (cosetK₁ : coset H K₁)
  (cosetK₂ : coset H K₂)
  (h₁ h₂ g₁ g₂ x : MyGroup)
  (H_h₁ : H h₁) (H_h₂ : H h₂)
  (h₁g₁_eq_x : mul h₁ g₁ = x) (h₂g₂_eq_x : mul h₂ g₂ = x) :
  ∀ y, (∃ h, H h ∧ y = mul h g₁) → (∃ h, H h ∧ y = mul h g₂):= by
  intro y h

  cases' h with w hwywg₁
  have hywg₁ : y = mul w g₁ := And.right hwywg₁

  -- Use the hypothesis about h₁ and g₁
  have hxx : x = x := rfl
  have hh₂g₂ : mul h₂ g₂ = x := h₂g₂_eq_x
  have hh₁g₁ : (mul h₁ g₁) = x := h₁g₁_eq_x
  have hh₁g₁h₂g₂ : mul h₁ g₁ = mul h₂ g₂ := by rw[hh₁g₁, hh₂g₂]
  have h₀ : mul (inv h₁) (mul h₁ g₁) = mul (inv h₁) (mul h₂ g₂) := by rw[hh₁g₁h₂g₂]
  have hh₁assoc : mul (inv h₁) (mul h₁ g₁) = mul (mul (inv h₁) h₁) g₁ := And.left (axassoc (inv h₁) h₁ g₁)
  have hh₁inv : mul (inv h₁) h₁ = I := And.right (axinv h₁)
  rw [hh₁inv] at hh₁assoc
  have hg₁identity : mul I g₁ = g₁ := And.right (axid g₁)
  rw [hg₁identity] at hh₁assoc
  rw [hh₁assoc] at h₀
  have hinvh₁h₂assoc : mul (inv h₁) (mul h₂ g₂) = mul (mul (inv h₁) h₂) g₂ := And.left (axassoc (inv h₁) h₂ g₂)
  rw [hinvh₁h₂assoc] at h₀
  rw [h₀] at hywg₁
  have hassoc : mul w (mul (mul (inv h₁) h₂) g₂) = mul (mul w (mul (inv h₁) h₂)) g₂ := And.left (axassoc w (mul (inv h₁) h₂) g₂)
  rw [hassoc] at hywg₁
  let v := mul w (mul (inv h₁) h₂)
  have hyvg₂ : y = mul v g₂ := hywg₁
  have Hv : H v := by
    have Hw : H w := And.left hwywg₁
    have Hinvh₁ : H (inv h₁) := subH.right.left h₁ H_h₁
    have Hinvh₁h₂ : H (mul (inv h₁) h₂) := subH.left (inv h₁) h₂ (And.intro Hinvh₁ H_h₂)
    have Hwinvh₁h₂ : H (mul w (mul (inv h₁) h₂)) := subH.left w (mul (inv h₁) h₂) (And.intro Hw Hinvh₁h₂)
    exact Hwinvh₁h₂
  have hfinal' : H v ∧ y = mul v g₂ := And.intro Hv hyvg₂
  have hfinal : ∃ h, H h ∧ y = mul h g₂ := by use v
  exact hfinal


theorem subgroup_coset_bijection (H K : MyGroup → Prop) (hH : subgroup H) (hK : coset H K) :
  ∃ f : MyGroup → MyGroup,
    (∀ x : MyGroup, H x → K (f x)) ∧
    (∀ x1 x2 : MyGroup, H x1 → H x2 → f x1 = f x2 → x1 = x2) ∧
    (∀ y : MyGroup, K y → ∃ x : MyGroup, H x ∧ f x = y)
  := by
    -- Extract the element g such that K is the coset H * g
    cases' hK with H_subgroup ex_g
    cases' ex_g with g K_eq

    let f := (mul · g)
    have h₁ : ∀ x : MyGroup, H x → K (f x) := by
      intro x Hx
      have eq_f_x : f x = mul x g := rfl
      have exists_h : ∃ h, H h ∧ f x = mul h g := Exists.intro x (And.intro Hx eq_f_x)
      exact (K_eq (f x)).mpr exists_h

    have h₂ : ∀ x1 x2 : MyGroup, H x1 → H x2 → f x1 = f x2 → x1 = x2 := by
      intros x1 x2 Hx1 Hx2 f_eq
      -- f_eq : f x1 = f x2 → mul x1 g = mul x2 g
      exact right_cancellation g x1 x2 f_eq

    have h₃ : ∀ y : MyGroup, K y → ∃ x : MyGroup, H x ∧ f x = y := by
      intro y Ky
      have exists_h := (K_eq y).mp Ky
      cases' exists_h with h hh
      have h_correct : H h ∧ f h = y := And.intro (And.left hh) (Eq.symm (And.right hh))
      exact Exists.intro h h_correct
    use f

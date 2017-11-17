/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import ..init .classes

universes u v w
hott_theory

namespace hott

section binary
variables {α : Type u} {β : Type v}
variable f : α → α → α
variable inv : α → α
variable one : α
local notation a * b := f a b
local notation a ⁻¹  := inv a
variable g : α → α → α
local notation a + b := g a b

def commutative        := ∀ a b, a * b = b * a
def associative        := ∀ a b c, (a * b) * c = a * (b * c)
def left_identity      := ∀ a, one * a = a
def right_identity     := ∀ a, a * one = a
def right_inverse      := ∀ a, a * a⁻¹ = one
def left_cancelative   := ∀ a b c, a * b = a * c → b = c
def right_cancelative  := ∀ a b c, a * b = c * b → a = c
def left_distributive  := ∀ a b c, a * (b + c) = a * b + a * c
def right_distributive := ∀ a b c, (a + b) * c = a * c + b * c
def right_commutative (h : β → α → β) := ∀ b a₁ a₂, h (h b a₁) a₂ = h (h b a₂) a₁
def left_commutative  (h : α → β → β) := ∀ a₁ a₂ b, h a₁ (h a₂ b) = h a₂ (h a₁ b)

lemma left_comm : commutative f → associative f → left_commutative f :=
assume hcomm hassoc, assume a b c, 
by rwr [←hassoc, hcomm a b, hassoc]

lemma right_comm : commutative f → associative f → right_commutative f :=
assume hcomm hassoc, assume a b c,
by rwr [hassoc, hcomm b c, ←hassoc]

end binary

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
-- set_option default_priority 100

variables {α : Type u}

@[hsimp] lemma mul_assoc [has_mul α] [h : is_associative α (*)] : ∀ a b c : α, a * b * c = a * (b * c) :=
h.assoc

@[hsimp] lemma mul_comm [has_mul α] [h : is_commutative α (*)] : ∀ a b : α, a * b = b * a :=
h.comm

@[hsimp] lemma one_mul [has_mul α] [has_one α] [h : is_left_id α (*) 1] : ∀ a : α, 1 * a = a :=
h.left_id

@[hsimp] lemma mul_one [has_mul α] [has_one α] [h : is_right_id α (*) 1] : ∀ a : α, a * 1 = a :=
h.right_id

@[hsimp] lemma mul_left_inv [has_mul α] [has_one α] [has_inv α] [h : is_left_inv α (*) has_inv.inv 1] : ∀ a : α, a⁻¹  * a = 1 :=
h.left_inv

-- alternate name
lemma inv_mul [has_mul α] [has_one α] [has_inv α] [h : is_left_inv α (*) has_inv.inv 1] : ∀ a : α, a⁻¹  * a = 1 :=
h.left_inv

@[hsimp] lemma mul_inv [has_mul α] [has_one α] [has_inv α] [h : is_right_inv α (*) has_inv.inv 1] : ∀ a : α, a * a⁻¹ = 1 :=
h.right_inv

-- alternate name
lemma mul_right_inv [has_mul α] [has_one α] [has_inv α] [h : is_right_inv α (*) has_inv.inv 1] : ∀ a : α, a * a⁻¹ = 1 :=
h.right_inv

lemma mul_left_cancel [has_mul α] [h : is_left_cancel α (*)] : ∀ {a b c : α}, a * b = a * c → b = c :=
is_left_cancel.left_cancel

lemma mul_right_cancel [has_mul α] [h : is_right_cancel α (*)] : ∀ {a b c : α}, a * b = c * b → a = c :=
h.right_cancel

--class semigroup (α : Type u) extends has_mul α :=
--(mul_assoc : ∀ a b c : α, a * b * c = a * (b * c))

--class comm_semigroup (α : Type u) extends semigroup α :=
--(mul_comm : ∀ a b : α, a * b = b * a)

--class left_cancel_semigroup (α : Type u) extends semigroup α :=
--(mul_left_cancel : ∀ a b c : α, a * b = a * c → b = c)

--class right_cancel_semigroup (α : Type u) extends semigroup α :=
--(mul_right_cancel : ∀ a b c : α, a * b = c * b → a = c)

--class monoid (α : Type u) extends semigroup α, has_one α :=
--(one_mul : ∀ a : α, 1 * a = a) (mul_one : ∀ a : α, a * 1 = a)

--class comm_monoid (α : Type u) extends monoid α, comm_semigroup α

-- class group (α : Type u) extends , has_inv α :=
-- (mul_left_inv : ∀ a : α, a⁻¹ * a = 1)

--class comm_group (α : Type u) extends group α, comm_monoid α


@[hsimp] lemma mul_left_comm [has_mul α] [is_associative α (*)] [is_commutative α (*)] : ∀ a b c : α, a * (b * c) = b * (a * c) :=
left_comm has_mul.mul mul_comm mul_assoc

lemma mul_right_comm [has_mul α] [is_associative α (*)] [is_commutative α (*)]  : ∀ a b c : α, a * b * c = a * c * b :=
right_comm has_mul.mul mul_comm mul_assoc

lemma mul_left_cancel_iff [has_mul α] [is_left_cancel α (*)] {a b c : α} : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, by intro h; rwr h⟩

lemma mul_right_cancel_iff [has_mul α] [is_right_cancel α (*)] {a b c : α} : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, by intro h; rwr h⟩

-- TODO(Jeremy): get rid of is_right_inv etc.
class is_group (α : Type _) (op : α → α → α) (o : α) (i : α → α) extends
  is_associative α op,
  is_left_id α op o,
  is_right_id α op o,
  is_left_inv α op i o,
  is_right_inv α op i o

/-
@[simp] lemma mul_right_inv (a : α) : a * a⁻¹ = 1 :=
have a⁻¹⁻¹ * a⁻¹ = 1, by rw mul_left_inv,
by rwa [inv_inv] at this
-/

section
variables [has_mul α] [has_inv α] [has_one α] [is_group α (*) (has_one.one α) has_inv.inv]

@[hsimp] lemma inv_mul_cancel_left (a b : α) : a⁻¹ * (a * b) = b :=
by rwr [←mul_assoc, inv_mul, one_mul]

@[hsimp] lemma inv_mul_cancel_right (a b : α) : a * b⁻¹ * b = a :=
by rwr [mul_assoc, inv_mul, mul_one]

lemma mul_inv_cancel_left (a b : α) : a * (a⁻¹ * b) = b :=
by rwr [← mul_assoc, mul_right_inv, one_mul]

lemma mul_inv_cancel_right (a b : α) : a * b * b⁻¹ = a :=
by rwr [mul_assoc, mul_right_inv, mul_one]

lemma inv_eq_of_mul_eq_one {a b : α} (h : a * b = 1) : a⁻¹ = b :=
by rwr [← mul_one a⁻¹, ←h, ←mul_assoc, inv_mul, one_mul]

@[hsimp] lemma one_inv : (1 : α)⁻¹ = 1 :=
inv_eq_of_mul_eq_one (one_mul 1)

@[hsimp] lemma inv_inv (a : α) : (a⁻¹)⁻¹ = a :=
inv_eq_of_mul_eq_one (mul_left_inv a)

lemma inv_inj {a b : α} (h : a⁻¹ = b⁻¹) : a = b :=
by rwr [←(inv_inv a), h, inv_inv]

-- TODO(Jeremy): why does this fail without the ←?
lemma group.mul_left_cancel {a b c : α} (h : a * b = a * c) : b = c :=
have a⁻¹ * (a * b) = b, by rwr inv_mul_cancel_left,
begin rwr [h, inv_mul_cancel_left] at this, rwr [←this] end

lemma group.mul_right_cancel {a b c : α} (h : a * b = c * b) : a = c :=
have a * b * b⁻¹ = a, by rwr mul_inv_cancel_right,
begin simp [h] at this, rw this end

/-
instance group.to_left_cancel_semigroup [s : group α] : left_cancel_semigroup α :=
{ s with mul_left_cancel := @group.mul_left_cancel α s }

instance group.to_right_cancel_semigroup [s : group α] : right_cancel_semigroup α :=
{ s with mul_right_cancel := @group.mul_right_cancel α s }
-/



@[simp] lemma mul_inv_rev [group α] (a b : α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
inv_eq_of_mul_eq_one begin rwr [mul_assoc, ← mul_assoc b, mul_right_inv, one_mul, mul_right_inv] end

lemma eq_inv_of_eq_inv [group α] {a b : α} (h : a = b⁻¹) : b = a⁻¹ :=
by simp [h]

lemma eq_inv_of_mul_eq_one [group α] {a b : α} (h : a * b = 1) : a = b⁻¹ :=
have a⁻¹ = b, from inv_eq_of_mul_eq_one h,
by simp [this.symm]

lemma eq_mul_inv_of_mul_eq [group α] {a b c : α} (h : a * c = b) : a = b * c⁻¹ :=
by simp [h.symm]

lemma eq_inv_mul_of_mul_eq [group α] {a b c : α} (h : b * a = c) : a = b⁻¹ * c :=
by simp [h.symm]

lemma inv_mul_eq_of_eq_mul [group α] {a b c : α} (h : b = a * c) : a⁻¹ * b = c :=
by simp [h]

lemma mul_inv_eq_of_eq_mul [group α] {a b c : α} (h : a = c * b) : a * b⁻¹ = c :=
by simp [h]

lemma eq_mul_of_mul_inv_eq [group α] {a b c : α} (h : a * c⁻¹ = b) : a = b * c :=
by simp [h.symm]

lemma eq_mul_of_inv_mul_eq [group α] {a b c : α} (h : b⁻¹ * a = c) : a = b * c :=
by simp [h.symm, mul_inv_cancel_left]

lemma mul_eq_of_eq_inv_mul [group α] {a b c : α} (h : b = a⁻¹ * c) : a * b = c :=
by rw [h, mul_inv_cancel_left]

lemma mul_eq_of_eq_mul_inv [group α] {a b c : α} (h : a = c * b⁻¹) : a * b = c :=
by simp [h]

lemma mul_inv [comm_group α] (a b : α) : (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
by rw [mul_inv_rev, mul_comm]

/- αdditive "sister" structures.
   Example, add_semigroup mirrors semigroup.
   These structures exist just to help automation.
   In an alternative design, we could have the binary operation as an
   extra argument for semigroup, monoid, group, etc. However, the lemmas
   would be hard to index since they would not contain any constant.
   For example, mul_assoc would be

   lemma mul_assoc {α : Type u} {op : α → α → α} [semigroup α op] :
                   ∀ a b c : α, op (op a b) c = op a (op b c) :=
    semigroup.mul_assoc

   The simplifier cannot effectively use this lemma since the pattern for
   the left-hand-side would be

        ?op (?op ?a ?b) ?c

   Remark: we use a tactic for transporting theorems from the multiplicative fragment
   to the additive one.
-/

/-
class add_semigroup (α : Type u) extends has_add α :=
(add_assoc : ∀ a b c : α, a + b + c = a + (b + c))

class add_comm_semigroup (α : Type u) extends add_semigroup α :=
(add_comm : ∀ a b : α, a + b = b + a)

class add_left_cancel_semigroup (α : Type u) extends add_semigroup α :=
(add_left_cancel : ∀ a b c : α, a + b = a + c → b = c)

class add_right_cancel_semigroup (α : Type u) extends add_semigroup α :=
(add_right_cancel : ∀ a b c : α, a + b = c + b → a = c)

class add_monoid (α : Type u) extends add_semigroup α, has_zero α :=
(zero_add : ∀ a : α, 0 + a = a) (add_zero : ∀ a : α, a + 0 = a)

class add_comm_monoid (α : Type u) extends add_monoid α, add_comm_semigroup α

class add_group (α : Type u) extends add_monoid α, has_neg α :=
(add_left_neg : ∀ a : α, -a + a = 0)

class add_comm_group (α : Type u) extends add_group α, add_comm_monoid α

open tactic

meta def transport_with_dict (dict : name_map name) (src : name) (tgt : name) : command :=
copy_decl_using dict src tgt
>> copy_attribute `reducible src tt tgt
>> copy_attribute `simp src tt tgt
>> copy_attribute `instance src tt tgt

/- Transport multiplicative to additive -/

meta def transport_multiplicative_to_additive (ls : list (name × name)) : command :=
let dict := rb_map.of_list ls in
ls.foldl (λ t ⟨src, tgt⟩, do
  env ← get_env,
  if (env.get tgt).to_bool = ff
  then t >> transport_with_dict dict src tgt
  else t)
skip

run_cmd transport_multiplicative_to_additive
  [/- map operations -/
   (`has_mul.mul, `has_add.add), (`has_one.one, `has_zero.zero), (`has_inv.inv, `has_neg.neg),
   (`has_mul, `has_add), (`has_one, `has_zero), (`has_inv, `has_neg),
   /- map constructors -/
   (`has_mul.mk, `has_add.mk), (`has_one, `has_zero.mk), (`has_inv, `has_neg.mk),
   /- map structures -/
   (`semigroup, `add_semigroup),
   (`monoid, `add_monoid),
   (`group, `add_group),
   (`comm_semigroup, `add_comm_semigroup),
   (`comm_monoid, `add_comm_monoid),
   (`comm_group, `add_comm_group),
   (`left_cancel_semigroup, `add_left_cancel_semigroup),
   (`right_cancel_semigroup, `add_right_cancel_semigroup),
   (`left_cancel_semigroup.mk, `add_left_cancel_semigroup.mk),
   (`right_cancel_semigroup.mk, `add_right_cancel_semigroup.mk),
   /- map instances -/
   (`semigroup.to_has_mul, `add_semigroup.to_has_add),
   (`monoid.to_has_one, `add_monoid.to_has_zero),
   (`group.to_has_inv, `add_group.to_has_neg),
   (`comm_semigroup.to_semigroup, `add_comm_semigroup.to_add_semigroup),
   (`monoid.to_semigroup, `add_monoid.to_add_semigroup),
   (`comm_monoid.to_monoid, `add_comm_monoid.to_add_monoid),
   (`comm_monoid.to_comm_semigroup, `add_comm_monoid.to_add_comm_semigroup),
   (`group.to_monoid, `add_group.to_add_monoid),
   (`comm_group.to_group, `add_comm_group.to_add_group),
   (`comm_group.to_comm_monoid, `add_comm_group.to_add_comm_monoid),
   (`left_cancel_semigroup.to_semigroup, `add_left_cancel_semigroup.to_add_semigroup),
   (`right_cancel_semigroup.to_semigroup, `add_right_cancel_semigroup.to_add_semigroup),
   /- map projections -/
   (`semigroup.mul_assoc, `add_semigroup.add_assoc),
   (`comm_semigroup.mul_comm, `add_comm_semigroup.add_comm),
   (`left_cancel_semigroup.mul_left_cancel, `add_left_cancel_semigroup.add_left_cancel),
   (`right_cancel_semigroup.mul_right_cancel, `add_right_cancel_semigroup.add_right_cancel),
   (`monoid.one_mul, `add_monoid.zero_add),
   (`monoid.mul_one, `add_monoid.add_zero),
   (`group.mul_left_inv, `add_group.add_left_neg),
   (`group.mul, `add_group.add),
   (`group.mul_assoc, `add_group.add_assoc),
   /- map lemmas -/
   (`mul_assoc, `add_assoc),
   (`mul_comm, `add_comm),
   (`mul_left_comm, `add_left_comm),
   (`mul_right_comm, `add_right_comm),
   (`one_mul, `zero_add),
   (`mul_one, `add_zero),
   (`mul_left_inv, `add_left_neg),
   (`mul_left_cancel, `add_left_cancel),
   (`mul_right_cancel, `add_right_cancel),
   (`mul_left_cancel_iff, `add_left_cancel_iff),
   (`mul_right_cancel_iff, `add_right_cancel_iff),
   (`inv_mul_cancel_left, `neg_add_cancel_left),
   (`inv_mul_cancel_right, `neg_add_cancel_right),
   (`eq_inv_mul_of_mul_eq, `eq_neg_add_of_add_eq),
   (`inv_eq_of_mul_eq_one, `neg_eq_of_add_eq_zero),
   (`inv_inv, `neg_neg),
   (`mul_right_inv, `add_right_neg),
   (`mul_inv_cancel_left, `add_neg_cancel_left),
   (`mul_inv_cancel_right, `add_neg_cancel_right),
   (`mul_inv_rev, `neg_add_rev),
   (`mul_inv, `neg_add),
   (`inv_inj, `neg_inj),
   (`group.mul_left_cancel, `add_group.add_left_cancel),
   (`group.mul_right_cancel, `add_group.add_right_cancel),
   (`group.to_left_cancel_semigroup, `add_group.to_left_cancel_add_semigroup),
   (`group.to_right_cancel_semigroup, `add_group.to_right_cancel_add_semigroup),
   (`eq_inv_of_eq_inv, `eq_neg_of_eq_neg),
   (`eq_inv_of_mul_eq_one, `eq_neg_of_add_eq_zero),
   (`eq_mul_inv_of_mul_eq, `eq_add_neg_of_add_eq),
   (`inv_mul_eq_of_eq_mul, `neg_add_eq_of_eq_add),
   (`mul_inv_eq_of_eq_mul, `add_neg_eq_of_eq_add),
   (`eq_mul_of_mul_inv_eq, `eq_add_of_add_neg_eq),
   (`eq_mul_of_inv_mul_eq, `eq_add_of_neg_add_eq),
   (`mul_eq_of_eq_inv_mul, `add_eq_of_eq_neg_add),
   (`mul_eq_of_eq_mul_inv, `add_eq_of_eq_add_neg),
   (`one_inv, `neg_zero)
]

instance add_semigroup_to_is_eq_associative [add_semigroup α] : is_associative α (+) :=
⟨add_assoc⟩

instance add_comm_semigroup_to_is_eq_commutative [add_comm_semigroup α] : is_commutative α (+) :=
⟨add_comm⟩

def neg_add_self := @add_left_neg
def add_neg_self := @add_right_neg
def eq_of_add_eq_add_left := @add_left_cancel
def eq_of_add_eq_add_right := @add_right_cancel

@[reducible] protected def algebra.sub [add_group α] (a b : α) : α :=
a + -b

instance add_group_has_sub [add_group α] : has_sub α :=
⟨algebra.sub⟩

@[simp] lemma sub_eq_add_neg [add_group α] (a b : α) : a - b = a + -b :=
rfl

lemma sub_self [add_group α] (a : α) : a - a = 0 :=
add_right_neg a

lemma sub_add_cancel [add_group α] (a b : α) : a - b + b = a :=
neg_add_cancel_right a b

lemma add_sub_cancel [add_group α] (a b : α) : a + b - b = a :=
add_neg_cancel_right a b

lemma add_sub_assoc [add_group α] (a b c : α) : a + b - c = a + (b - c) :=
by rw [sub_eq_add_neg, add_assoc, ←sub_eq_add_neg]

lemma eq_of_sub_eq_zero [add_group α] {a b : α} (h : a - b = 0) : a = b :=
have 0 + b = b, by rw zero_add,
have (a - b) + b = b, by rwa h,
by rwa [sub_eq_add_neg, neg_add_cancel_right] at this

lemma sub_eq_zero_of_eq [add_group α] {a b : α} (h : a = b) : a - b = 0 :=
by rw [h, sub_self]

lemma sub_eq_zero_iff_eq [add_group α] {a b : α} : a - b = 0 ↔ a = b :=
⟨eq_of_sub_eq_zero, sub_eq_zero_of_eq⟩

lemma zero_sub [add_group α] (a : α) : 0 - a = -a :=
zero_add (-a)

lemma sub_zero [add_group α] (a : α) : a - 0 = a :=
by rw [sub_eq_add_neg, neg_zero, add_zero]

lemma sub_ne_zero_of_ne [add_group α] {a b : α} (h : a ≠ b) : a - b ≠ 0 :=
begin
  intro hab,
  apply h,
  apply eq_of_sub_eq_zero hab
end

lemma sub_neg_eq_add [add_group α] (a b : α) : a - (-b) = a + b :=
by rw [sub_eq_add_neg, neg_neg]

lemma neg_sub [add_group α] (a b : α) : -(a - b) = b - a :=
neg_eq_of_add_eq_zero (by rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, neg_add_cancel_left, add_right_neg])

lemma add_sub [add_group α] (a b c : α) : a + (b - c) = a + b - c :=
by simp

lemma sub_add_eq_sub_sub_swap [add_group α] (a b c : α) : a - (b + c) = a - c - b :=
by simp

lemma add_sub_add_right_eq_sub [add_group α] (a b c : α) : (a + c) - (b + c) = a - b :=
by rw [sub_add_eq_sub_sub_swap]; simp

lemma eq_sub_of_add_eq [add_group α] {a b c : α} (h : a + c = b) : a = b - c :=
by simp [h.symm]

lemma sub_eq_of_eq_add [add_group α] {a b c : α} (h : a = c + b) : a - b = c :=
by simp [h]

lemma eq_add_of_sub_eq [add_group α] {a b c : α} (h : a - c = b) : a = b + c :=
by simp [h.symm]

lemma add_eq_of_eq_sub [add_group α] {a b c : α} (h : a = c - b) : a + b = c :=
by simp [h]

lemma sub_add_eq_sub_sub [add_comm_group α] (a b c : α) : a - (b + c) = a - b - c :=
by simp

lemma neg_add_eq_sub [add_comm_group α] (a b : α) : -a + b = b - a :=
by simp

lemma sub_add_eq_add_sub [add_comm_group α] (a b c : α) : a - b + c = a + c - b :=
by simp

lemma sub_sub [add_comm_group α] (a b c : α) : a - b - c = a - (b + c) :=
by simp

lemma sub_add [add_comm_group α] (a b c : α) : a - b + c = a - (b - c) :=
by simp

lemma add_sub_add_left_eq_sub [add_comm_group α] (a b c : α) : (c + a) - (c + b) = a - b :=
by simp

lemma eq_sub_of_add_eq' [add_comm_group α] {a b c : α} (h : c + a = b) : a = b - c :=
by simp [h.symm]

lemma sub_eq_of_eq_add' [add_comm_group α] {a b c : α} (h : a = b + c) : a - b = c :=
by simp [h]

lemma eq_add_of_sub_eq' [add_comm_group α] {a b c : α} (h : a - b = c) : a = b + c :=
by simp [h.symm]

lemma add_eq_of_eq_sub' [add_comm_group α] {a b c : α} (h : b = c - a) : a + b = c :=
begin simp [h], rw [add_comm c, add_neg_cancel_left] end

lemma sub_sub_self [add_comm_group α] (a b : α) : a - (a - b) = b :=
begin simp, rw [add_comm b, add_neg_cancel_left] end

lemma add_sub_comm [add_comm_group α] (a b c d : α) : a + b - (c + d) = (a - c) + (b - d) :=
by simp

lemma sub_eq_sub_add_sub [add_comm_group α] (a b c : α) : a - b = c - b + (a - c) :=
by simp

lemma neg_neg_sub_neg [add_comm_group α] (a b : α) : - (-a - -b) = a - b :=
by simp

/- The following lemmas generate too many instances for rsimp -/
attribute [no_rsimp]
  mul_assoc mul_comm mul_left_comm
  add_assoc add_comm add_left_comm


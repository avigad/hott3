/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/

import ..init .classes .group

universes u v w
hott_theory

namespace hott

/- section Groups: move -/
 
structure Group :=
(carrier : Type u)
(op : carrier → carrier → carrier)
(id : carrier)
(inv : carrier → carrier)
(is_group : is_group carrier op id inv)

instance has_coe_to_sort_Group : has_coe_to_sort Group :=
⟨Type u, λ G : Group.{u}, G.carrier⟩

instance is_group_Group (G : Group) : is_group (G.carrier) (G.op) (G.id) (G.inv) :=
G.is_group

@[simp] def Group_right_inv (G : Group) := is_right_inv.right_inv (G.op) (G.inv) (G.id)

section
  variable G : Group
  variables a b c : G

  local infix * := G.op
  local notation 1 := G.id
  local postfix ⁻¹ := G.inv

  /- doesn't need the underscores in the classical library-/
  example : a * a⁻¹ * b = b :=
  begin
    rwr [is_right_inv.right_inv (G.op) _ _, is_left_id.left_id (G.op) _ _ ]
  end

  example : a * a⁻¹ * b = b :=
  begin
  --  rwr [Group_right_inv, Group_left_id]
  end
 
  /- works in classical library
  example : a * a⁻¹ * b = b :=
  by simp
  -/

end

end hott

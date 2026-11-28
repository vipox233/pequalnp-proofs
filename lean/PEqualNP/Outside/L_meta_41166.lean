import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41166

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808936 * 2 ^ 32 + 4272483464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x0020660680cd1c59#64 ++ 0x40020660680cd1c5#64 ++ 0xe063ee0f81ff3cff#64 ++ 0xbe063ee0f81ff3cf#64 : BitVec 256),
   (0x008d00b1422241a0#64 ++ 0x8008d00b1422241a#64 ++ 0xe19d13f1c623c7ff#64 ++ 0x6e19d13f1c623c7f#64 : BitVec 256),
   (0x1616185a5834e8c5#64 ++ 0x01616185a5834e8c#64 ++ 0xbe1e1c7e783cf8ce#64 ++ 0xfbe1e1c7e783cf8c#64 : BitVec 256),
   (0x2b601f002d40b606#64 ++ 0x02b601f002d40b60#64 ++ 0x7fe01f807fc0ff0d#64 ++ 0xf7fe01f807fc0ff0#64 : BitVec 256),
   (0x4ddfa00077bb0008#64 ++ 0x04ddfa00077bb000#64 ++ 0x5fffe0007fff000b#64 ++ 0xf5fffe0007fff000#64 : BitVec 256),
   (0x8ffbdfed80000000#64 ++ 0x08ffbdfed8000000#64 ++ 0x8fffffff80000007#64 ++ 0xe8fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [9, 2]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [13, 7]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe063ee0f81ff3cff 0xbe063ee0f81ff3cf

def z1 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xe19d13f1c623c7ff 0x6e19d13f1c623c7f

def z2 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1e1c7e783cf8ce 0xfbe1e1c7e783cf8c

def z3 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x1e600c0039c03800 0x91e600c0039c0380

def z4 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7fe01f807fc0ff0d 0xf7fe01f807fc0ff0

def z5 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5fffe0007fff000b 0xf5fffe0007fff000

def z6 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8fffffff80000007 0xe8fffffff8000000

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0x618013804600c70d 0x6618013804600c70

def z8 : W := mkw 0x2bed1fb16f62f7a6 0x82bed1fb16f62f7a 0xfffd1ff1ffe3ffff 0xffffd1ff1ffe3fff

def z9 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x1e62e00039dc0000 0x91e62e00039dc000

def z10 : W := mkw 0x89e9c7a580000000 0x089e9c7a58000000 0x01e1e38180000001 0x001e1e3818000000

def z11 : W := mkw 0x4089a000028b0008 0x04089a000028b000 0x0001e00000030000 0x00001e0000003000

def z12 : W := mkw 0x0416000050300000 0x0041600005030000 0x1e1e0000783c000a 0xf1e1e0000783c000

def z13 : W := mkw 0x5fdfb85a7fbfe8cd 0x05fdfb85a7fbfe8c 0xfffffc7e7ffff8cf 0xffffffc7e7ffff8c

def z14 : W := mkw 0x89edc7b5c22241a0 0x889edc7b5c22241a 0xe1fdf3f1c623c7ff 0x6e1fdf3f1c623c7f

def z15 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x019c11f04600c300 0x4019c11f04600c30

def z16 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0xfffff3f1ffffc7ff 0xffffff3f1ffffc7f

def z17 : W := mkw 0x0020460480000000 0x0002046048000000 0x8063ee0f80000007 0xa8063ee0f8000000

def z18 : W := mkw 0x8ffbffef80cd1c59 0x48ffbffef80cd1c5 0xefffffff81ff3cff 0xfefffffff81ff3cf

def z19 : W := mkw 0x0940000025000000 0x0094000002500000 0x5fe000007fc00009 0xf5fe000007fc0000

def z20 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z21 : W := mkw 0x008d20b142ab41a8 0x8008d20b142ab41a 0xe1fff3f1c7ffc7ff 0xfe1fff3f1c7ffc7f

def z22 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xa062ee0f81dc3cf4 0x9a062ee0f81dc3cf

def z23 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x801fe07f80000002 0x0801fe07f8000000

def z24 : W := mkw 0x8fffdffdc22241a0 0x88fffdffdc22241a 0xefffffffc623c7ff 0xeefffffffc623c7f

def z25 : W := mkw 0x0612184800000000 0x0061218480000000 0x8e1e1c7e00000006 0xe8e1e1c7e0000000

def z26 : W := mkw 0x9fffdfffd834e8c5 0x09fffdfffd834e8c 0xbffffffff83cf8cf 0xfbffffffff83cf8c

def z27 : W := mkw 0x5ddfa0127fbfe8cd 0x05ddfa0127fbfe8c 0x7fffe0007ffff8cb 0xf7fffe0007ffff8c

def z28 : W := mkw 0x2b605f06ad44be57 0x42b605f06ad44be5 0xffe01f8fffc0fffd 0xfffe01f8fffc0fff

def z29 : W := mkw 0x1612184a1814a845 0x01612184a1814a84 0x1e020c0e381c3800 0x91e020c0e381c380

def z30 : W := mkw 0x00ad66b7c2ef5df9 0xc00ad66b7c2ef5df 0xe07fee7f81ff3cff 0xbe07fee7f81ff3cf

def z31 : W := mkw 0x200000002d40b606 0x0200000002d40b60 0x1000000039c03800 0x11000000039c0380

def z32 : W := mkw 0x008d000042220000 0x0008d00004222000 0xe19d0201c62304ff 0x6e19d0201c62304f

def z33 : W := mkw 0x1612184a1814a845 0x01612184a1814a84 0x9e1e1c7e381c3806 0xf9e1e1c7e381c380

def z34 : W := mkw 0x8ffbdfed80401400 0x08ffbdfed8040140 0xefffffff81c03c0f 0xfefffffff81c03c0

def z35 : W := mkw 0x8412c04c80000000 0x08412c04c8000000 0x0002e00e00000000 0x00002e00e0000000

def z36 : W := mkw 0x00ad66b7c2ef5df9 0xc00ad66b7c2ef5df 0xe1ffffffc7ffffff 0xfe1ffffffc7fffff

def z37 : W := mkw 0x0020060000401400 0x0002006000040140 0x00600c0001c03800 0x900600c0001c0380

def z38 : W := mkw 0x4d72e606b5dd1c59 0x44d72e606b5dd1c5 0x1e62ec0e39dc3800 0x91e62ec0e39dc380

def z39 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0x8063ec0f81ff38f2 0x98063ec0f81ff38f

def z40 : W := mkw 0x100400125834e8c5 0x0100400125834e8c 0x30000000783cf8c8 0x130000000783cf8c

def z41 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0x0062ec0e01dc3800 0x90062ec0e01dc380

def z42 : W := mkw 0x16367e5ed8fdfcdd 0x416367e5ed8fdfcd 0xfe7ffe7ff9fffcff 0xffe7ffe7ff9fffcf

def z43 : W := mkw 0x500420127fbfe8cd 0x0500420127fbfe8c 0x700000007ffff8c8 0x1700000007ffff8c

def z44 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7e600e0039c03c0d 0xb7e600e0039c03c0

def z45 : W := mkw 0x8ffbffed80c91418 0x48ffbffed80c9141 0xcfffffff81c30437 0xecfffffff81c3043

def z46 : W := mkw 0x00006006808d0859 0x400006006808d085 0x8003e00f803f00f2 0x08003e00f803f00f

def z47 : W := mkw 0x008900a102020120 0x8008900a10202012 0x4181038186030731 0x0418103818603073

def z48 : W := mkw 0x00ad6606c2ef1c59 0x400ad6606c2ef1c5 0xe1ffee0fc7ff3cff 0xfe1ffee0fc7ff3cf

def z49 : W := mkw 0x1200185a0804e8c5 0x01200185a0804e8c 0xa0001c7e0000f8c4 0x0a0001c7e0000f8c

def z50 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z51 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0xffe11f81ffe3ffff 0xfffe11f81ffe3fff

def z52 : W := mkw 0xcfdfb9e977bb0008 0x0cfdfb9e977bb000 0x5ffff1f07fff000b 0xf5ffff1f07fff000

def z53 : W := mkw 0x6fffbfb17ffbf7ae 0x86fffbfb17ffbf7a 0xfffffff1ffffffff 0xffffffff1fffffff

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0010201802304ff 0x2e0010201802304f

def z55 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xefffffff802304ff 0xeefffffff802304f

def z56 : W := mkw 0x0940000025000000 0x0094000002500000 0x1e60000039c00000 0x91e60000039c0000

def z57 : W := mkw 0x0004000050300000 0x0000400005030000 0x10000000783c0008 0x110000000783c000

def z58 : W := mkw 0x00040010422241a0 0x800040010422241a 0x618013804623c7fd 0x6618013804623c7f

def z59 : W := mkw 0x0b601f0025000000 0x00b601f002500000 0x5fe01f807fc0000d 0xf5fe01f807fc0000

def z60 : W := mkw 0x4ddfa0a177bb0128 0x84ddfa0a177bb012 0x5fffe381ffff073b 0xf5fffe381ffff073

def z61 : W := mkw 0x6fffbf007ffbb60e 0x06fffbf007ffbb60 0x7fffff807fffff0f 0xf7fffff807fffff0

def z62 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xa19c11f04620c3ce 0x6a19c11f04620c3c

def z63 : W := mkw 0x0020460480401400 0x0002046048040140 0xe063ee0f81c03c0f 0xbe063ee0f81c03c0

def z64 : W := mkw 0x0ddb800000000000 0x00ddb80000000000 0x0fffe00000000003 0xe0fffe0000000000

def z65 : W := mkw 0x4004200077bb0008 0x04004200077bb000 0x500000007fff0008 0x1500000007fff000

def z66 : W := mkw 0x0020460680441c51 0x40020460680441c5 0xa0000e0f80003cf4 0x0a0000e0f80003cf

def z67 : W := mkw 0x0004001040204080 0x0000400104020408 0xa01c10704020c0ce 0x6a01c10704020c0c

def z68 : W := mkw 0x169f18fb5a36e9e5 0x8169f18fb5a36e9e 0xff9f1ffffe3fffff 0xfff9f1ffffe3ffff

def z69 : W := mkw 0x200000002d40b606 0x0200000002d40b60 0x700000007fc0ff08 0x1700000007fc0ff0

def z70 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x819ff3ff80000007 0x6819ff3ff8000000

def z71 : W := mkw 0x0020460680441c51 0x40020460680441c5 0xa063ee0f80003cf7 0xaa063ee0f80003cf

def z72 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x5e63e00039ff000b 0xb5e63e00039ff000

def z73 : W := mkw 0x169f18f95a32e1a4 0x8169f18f95a32e1a 0xff9d13f1fe23c7ff 0x6ff9d13f1fe23c7f

def z74 : W := mkw 0x161618585830e084 0x0161618585830e08 0x1e1e1070783cc00a 0xf1e1e1070783cc00

def z75 : W := mkw 0x0000000200441c51 0x40000000200441c5 0x2000000000003cf0 0x02000000000003cf

def z76 : W := mkw 0x4d56a00075b90008 0x04d56a00075b9000 0x1e7ee00079fc000a 0xf1e7ee00079fc000

def z77 : W := mkw 0x22201f000840b606 0x022201f000840b60 0x00000c0000003800 0x000000c000000380

def z78 : W := mkw 0x82205fed80000000 0x082205fed8000000 0x80001fff80000004 0x080001fff8000000

def z79 : W := mkw 0x0000000000000000 0x0000000000000000 0x1e00000078000008 0xf1e0000007800000

def z80 : W := mkw 0x2960070025401602 0x0296007002540160 0x41e0038007c00701 0x041e0038007c0070

def z81 : W := mkw 0x869bd8ed80000000 0x0869bd8ed8000000 0x8e1ffc7f80000006 0xe8e1ffc7f8000000

def z82 : W := mkw 0x40002000278b0008 0x040002000278b000 0x4000000007c30000 0x04000000007c3000

def z83 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0x6061e20181ff3cf9 0x16061e20181ff3cf

def z84 : W := mkw 0x2be91fa12f42b726 0x82be91fa12f42b72 0x7fe11f81ffc3ff3d 0xf7fe11f81ffc3ff3

def z85 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x1e7fe00039ff0002 0x91e7fe00039ff000

def z86 : W := mkw 0x49cda00077bb0008 0x049cda00077bb000 0x51e1e0007fff0009 0x151e1e0007fff000

def z87 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x819d13f1802300f7 0x6819d13f1802300f

def z88 : W := mkw 0x849fc0fdc22241a0 0x8849fc0fdc22241a 0xe19ff3ffc623c7ff 0x6e19ff3ffc623c7f

def z89 : W := mkw 0x2b607f06adcdbe5f 0x42b607f06adcdbe5 0xffe3ff8fffffffff 0xfffe3ff8ffffffff

def z90 : W := mkw 0x1416005a503448c1 0x01416005a503448c 0xa01e0c7e003c38ce 0xba01e0c7e003c38c

def z91 : W := mkw 0x22207f0688cdbe5f 0x422207f0688cdbe5 0xe063ff8f81ffffff 0xbe063ff8f81fffff

def z92 : W := mkw 0x0004001040204080 0x0000400104020408 0x200000004020c0c8 0x0200000004020c0c

def z93 : W := mkw 0x4412a00010990008 0x04412a0001099000 0x0002e000001c0000 0x00002e000001c000

def z94 : W := mkw 0x800040ed80000000 0x0800040ed8000000 0x8000007f80000000 0x08000007f8000000

def z95 : W := mkw 0x008900a102020120 0x8008900a10202012 0x0001000180030030 0x0000100018003003

def z96 : W := mkw 0x1416005a503448c1 0x01416005a503448c 0x801e007e003c00c2 0x0801e007e003c00c

def z97 : W := mkw 0x008900a102020120 0x8008900a10202012 0x61811381c603c73d 0x661811381c603c73

def z98 : W := mkw 0x2b607f06adcdbe5f 0x42b607f06adcdbe5 0x1e62ec0e39dc3800 0x91e62ec0e39dc380

def z99 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8e7fec7f80000002 0x88e7fec7f8000000

def z100 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0xdfffe071ffff00fb 0xfdfffe071ffff00f

def z101 : W := mkw 0x8f72df4c80000000 0x08f72df4c8000000 0x0e62ec0e00000000 0x80e62ec0e0000000

def z102 : W := mkw 0x000000b1000041a0 0x8000000b1000041a 0xe18013f1c600c7fd 0x6e18013f1c600c7f

def z103 : W := mkw 0x0020060000401400 0x0002006000040140 0x4060020001c00401 0x04060020001c0040

def z104 : W := mkw 0x0020060000401400 0x0002006000040140 0x20000e0000003c04 0x020000e0000003c0

def z105 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xc063e20f81ff04f3 0x0c063e20f81ff04f

def z106 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe061ee0f81c33cf5 0x0e061ee0f81c33cf

def z107 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xa003ee0f803f3cf6 0x0a003ee0f803f3cf

def z108 : W := mkw 0x6b643f007ffbb60e 0x06b643f007ffbb60 0x7fe01f807fffff0d 0xf7fe01f807fffff0

def z109 : W := mkw 0x0020060000401400 0x0002006000040140 0x61e01f8047c0ff0d 0xf61e01f8047c0ff0

def z110 : W := mkw 0x0000200200cd1c59 0x40000200200cd1c5 0x6000000001ff3cf8 0x16000000001ff3cf

def z111 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe1e3ff8fc7ffffff 0xfe1e3ff8fc7fffff

def z112 : W := mkw 0x22201f000840b606 0x022201f000840b60 0x3e001f807800ff0c 0xf3e001f807800ff0

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0x4001020180030431 0x0400102018003043

def z114 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x819d11f1c623c3f2 0x4819d11f1c623c3f

def z115 : W := mkw 0x4ddf800077320000 0x04ddf80007732000 0x1f9c00007e000000 0x41f9c00007e00000

def z116 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x41ffe00007ff0003 0x041ffe00007ff000

def z117 : W := mkw 0x2020070000401602 0x0202007000040160 0x0000038000000700 0x0000003800000070

def z118 : W := mkw 0x0fdb984800000000 0x00fdb98480000000 0x8ffffc7e00000007 0xe8ffffc7e0000000

def z119 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x819d13f1c600c307 0x6819d13f1c600c30

def z120 : W := mkw 0x12207e5e88cdfcdd 0x412207e5e88cdfcd 0xe063fe7f81fffcff 0xbe063fe7f81fffcf

def z121 : W := mkw 0x008d00a142220000 0x0008d00a14222000 0xc19d13f1c623000f 0x6c19d13f1c623000

def z122 : W := mkw 0x008d000042220000 0x0008d00004222000 0x019c000046000000 0x4019c00004600000

def z123 : W := mkw 0x0000200000890008 0x0000020000089000 0x4063e00001ff000b 0xb4063e00001ff000

def z124 : W := mkw 0x22201f000840b606 0x022201f000840b60 0x20001f800000ff04 0x020001f800000ff0

def z125 : W := mkw 0x449fa00052bb0008 0x0449fa00052bb000 0x001fe000003f0002 0x0001fe000003f000

def z126 : W := mkw 0x3f761f5a7d74fec7 0x03f761f5a7d74fec 0xfffe1ffe7ffcffcf 0xffffe1ffe7ffcffc

def z127 : W := mkw 0xa2205fed8840b606 0x0a2205fed8840b60 0xa0001fff8000ff04 0x0a0001fff8000ff0

def z128 : W := mkw 0x8fdb99e900000000 0x08fdb99e90000000 0x0f9c11f000000000 0x40f9c11f00000000

def z129 : W := mkw 0xcddfe0edf7bb0008 0x0cddfe0edf7bb000 0xdfffe07fffff000b 0xfdfffe07fffff000

def z130 : W := mkw 0x8ffbdfef80040841 0x08ffbdfef8004084 0xafffffff803c38cf 0xfafffffff803c38c

def z131 : W := mkw 0x0020060000401400 0x0002006000040140 0x60600e0001c03c0d 0xb60600e0001c03c0

def z132 : W := mkw 0x82205fef80441c51 0x482205fef80441c5 0xa0001fff80003cf4 0x0a0001fff80003cf

def z133 : W := mkw 0x00a966a780cd1c59 0x400a966a780cd1c5 0xe1ffffff81ff3cff 0xfe1ffffff81ff3cf

def z134 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x3f801f807e00ff04 0x43f801f807e00ff0

def z135 : W := mkw 0x5f56b85a7dbde8cd 0x05f56b85a7dbde8c 0xbe7efc7e79fcf8ce 0xfbe7efc7e79fcf8c

def z136 : W := mkw 0x69e9a70027cb160a 0x069e9a70027cb160 0x41e1e38007c30701 0x041e1e38007c3070

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0000000002000ce 0x2a0000000002000c

def z138 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x1f9fe0007e3f0002 0x41f9fe0007e3f000

def z139 : W := mkw 0x8fdb99e900000000 0x08fdb99e90000000 0x0ffff1f000000003 0xe0ffff1f00000000

def z140 : W := mkw 0x020018000800a004 0x0020018000800a00 0x3e001c007800f80c 0xf3e001c007800f80

def z141 : W := mkw 0x8ffbffef808d0859 0x48ffbffef808d085 0x8fffffff803f00f7 0xe8fffffff803f00f

def z142 : W := mkw 0xaffbdfedad00a206 0x0affbdfedad00a20 0x9ffffffffe00c307 0xe9ffffffffe00c30

def z143 : W := mkw 0x49c9a000278b0008 0x049c9a000278b000 0x41e1e00007c30001 0x041e1e00007c3000

def z144 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x0fe01f8000000005 0xe0fe01f800000000

def z145 : W := mkw 0xcfffffedf7bb0008 0x0cfffffedf7bb000 0xdfffffffffff000f 0xfdfffffffffff000

def z146 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5ffde0007fc30001 0x45ffde0007fc3000

def z147 : W := mkw 0x169f18fb5a36e9e5 0x8169f18fb5a36e9e 0xbe1f1c7ff83ff8fe 0xfbe1f1c7ff83ff8f

def z148 : W := mkw 0x0000000200040841 0x0000000020004084 0xa0020c0e003c38ce 0xba0020c0e003c38c

def z149 : W := mkw 0x16365e5ed834e8c5 0x016365e5ed834e8c 0xbe7ffe7ff83cf8cf 0xfbe7ffe7ff83cf8c

def z150 : W := mkw 0x008d000042220000 0x0008d00004222000 0x419d00004623000b 0x6419d00004623000

def z151 : W := mkw 0x82a95fed80000000 0x082a95fed8000000 0x819d1fff80000007 0x6819d1fff8000000

def z152 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0x6062ec0e01ff3cf8 0x96062ec0e01ff3cf

def z153 : W := mkw 0x0dfbe60680cd1c59 0x40dfbe60680cd1c5 0xefffee0f81ff3cff 0xfefffee0f81ff3cf

def z154 : W := mkw 0x00040010422241a0 0x800040010422241a 0x600000004623c7f8 0x0600000004623c7f

def z155 : W := mkw 0x161618585830e084 0x0161618585830e08 0x1e1c10707800c000 0x41e1c10707800c00

def z156 : W := mkw 0x0020460480000000 0x0002046048000000 0x0061e20180000001 0x00061e2018000000

def z157 : W := mkw 0x9fffdfffda36e9e5 0x89fffdfffda36e9e 0xfffffffffe3fffff 0xffffffffffe3ffff

def z158 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x5fe2e0007fdc0009 0xf5fe2e0007fdc000

def z159 : W := mkw 0x2000000025401602 0x0200000002540160 0x4000000007c00700 0x04000000007c0070

def z160 : W := mkw 0x0000400480000000 0x0000040048000000 0x8003e00f80000002 0x08003e00f8000000

def z161 : W := mkw 0x008900a100000000 0x0008900a10000000 0xe19d13f1802304ff 0x6e19d13f1802304f

def z162 : W := mkw 0x8f72df4c80000000 0x08f72df4c8000000 0x8e7efc7e00000006 0xe8e7efc7e0000000

def z163 : W := mkw 0xefffffedfffbb60e 0x0efffffedfffbb60 0xffffffffffffff0f 0xfffffffffffffff0

def z164 : W := mkw 0xc49fe0edd2bb0008 0x0c49fe0edd2bb000 0x801fe07f803f0002 0x0801fe07f803f000

def z165 : W := mkw 0x0020660480c91418 0x40020660480c9141 0x4061e20181c30431 0x04061e20181c3043

def z166 : W := mkw 0x4004201077bb41a8 0x84004201077bb41a 0x700000007fffc7f8 0x1700000007fffc7f

def z167 : W := mkw 0x008900b1020241a0 0x8008900b1020241a 0xe18113f18603c7f5 0x0e18113f18603c7f

def z168 : W := mkw 0x2960070025401602 0x0296007002540160 0x5fe003807fc00709 0xf5fe003807fc0070

def z169 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x419d13f1c603c731 0x4419d13f1c603c73

def z170 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5f9c00007fff0008 0x55f9c00007fff000

def z171 : W := mkw 0xafffdffdef62f7a6 0x8afffdffdef62f7a 0xffffffffffe3ffff 0xfffffffffffe3fff

def z172 : W := mkw 0x449fa0b152bb41a8 0x8449fa0b152bb41a 0xe19ff3f1c63fc7ff 0x6e19ff3f1c63fc7f

def z173 : W := mkw 0xcfffffedd2bb0008 0x0cfffffedd2bb000 0x8fffffff803f0007 0xe8fffffff803f000

def z174 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x7ffff3807fffc70f 0xf7ffff3807fffc70

def z175 : W := mkw 0x008900a100000000 0x0008900a10000000 0xe19d13f1c600c70f 0x6e19d13f1c600c70

def z176 : W := mkw 0x20206606adcdbe5f 0x420206606adcdbe5 0xf063ee0fffffffff 0xbf063ee0ffffffff

def z177 : W := mkw 0x0ddf80b1422241a0 0x80ddf80b1422241a 0xeffff3f1c623c7ff 0xeeffff3f1c623c7f

def z178 : W := mkw 0x200000002d00a206 0x0200000002d00a20 0x100000007e00c300 0x0100000007e00c30

def z179 : W := mkw 0x0b601f000800a004 0x00b601f000800a00 0x3fe01f807800f80d 0xf3fe01f807800f80

def z180 : W := mkw 0x10246616d8fdfcdd 0x410246616d8fdfcd 0xf063ee0ff9fffcff 0xbf063ee0ff9fffcf

def z181 : W := mkw 0x4dffe606f7ff1c59 0x44dffe606f7ff1c5 0xffffee0fffff3cff 0xfffffee0fffff3cf

def z182 : W := mkw 0x8fffdffdc22241a0 0x88fffdffdc22241a 0x8fffffff802300f7 0xe8fffffff802300f

def z183 : W := mkw 0x0000000000000000 0x0000000000000000 0x018011804600c300 0x4018011804600c30

def z184 : W := mkw 0x49e9e604a7cb1418 0x449e9e604a7cb141 0x41e1e20187c30431 0x041e1e20187c3043

def z185 : W := mkw 0x069b18e900000000 0x0069b18e90000000 0x8f9f1fff80000007 0xe8f9f1fff8000000

def z186 : W := mkw 0x8960c70480000000 0x08960c7048000000 0x0060e00000000000 0x00060e0000000000

def z187 : W := mkw 0x22201f000840b606 0x022201f000840b60 0x61801f804600ff0d 0x661801f804600ff0

def z188 : W := mkw 0x008900a100000000 0x0008900a10000000 0x819d13f180000007 0x6819d13f18000000

def z189 : W := mkw 0x4dffe604f7fb1418 0x44dffe604f7fb141 0x5fffe201ffff043b 0xf5fffe201ffff043

def z190 : W := mkw 0x4ddfa0a177bb0008 0x04ddfa0a177bb000 0xdffff3f1ffff000f 0xfdffff3f1ffff000

def z191 : W := mkw 0x2ffb9f002d40b606 0x02ffb9f002d40b60 0x7fffff807fc0ff0f 0xf7fffff807fc0ff0

def z192 : W := mkw 0x2b4019002d00a206 0x02b4019002d00a20 0x1f8011807e00c300 0x41f8011807e00c30

def z193 : W := mkw 0x100000021814a845 0x0100000021814a84 0x10000000381c3800 0x110000000381c380

def z194 : W := mkw 0x008d000042220000 0x0008d00004222000 0x001d000000230002 0x0001d00000023000

def z195 : W := mkw 0x4dffa60077fb1408 0x04dffa60077fb140 0x7fffee007fff3c0f 0xf7fffee007fff3c0

def z196 : W := mkw 0x449fe006d2bf0859 0x4449fe006d2bf085 0x801fe00f803f00f2 0x0801fe00f803f00f

def z197 : W := mkw 0x6fffbf007ffbb60e 0x06fffbf007ffbb60 0x5fffec007fff380b 0xf5fffec007fff380

def z198 : W := mkw 0x4940a00025890008 0x04940a0002589000 0x0060e00001c00000 0x00060e00001c0000

def z199 : W := mkw 0xaffbdfed8840b606 0x0affbdfed8840b60 0xafffffff8000ff07 0xeafffffff8000ff0

def z200 : W := mkw 0xaffbffefadcdbe5f 0x4affbffefadcdbe5 0xffffffffffffffff 0xffffffffffffffff

def z201 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe0000e0f81ff3cfc 0x1e0000e0f81ff3cf

def z202 : W := mkw 0x16bf7effdafffdfd 0xc16bf7effdafffdf 0xffffffffffffffff 0xffffffffffffffff

def z203 : W := mkw 0x0089000002020000 0x0008900000202000 0x4181000006030001 0x0418100000603000

def z204 : W := mkw 0x32201f5a0844fec7 0x032201f5a0844fec 0xa0001ffe0000ffc4 0x0a0001ffe0000ffc

def z205 : W := mkw 0xaffbdfeda5401602 0x0affbdfeda540160 0xcfffffff87c00707 0xecfffffff87c0070

def z206 : W := mkw 0x0020260000c91408 0x00020260000c9140 0x6063ee0001ff3c0f 0xb6063ee0001ff3c0

def z207 : W := mkw 0x0ffb9f0000000000 0x00ffb9f000000000 0x0fffff8000000007 0xe0fffff800000000

def z208 : W := mkw 0x0bed1fb1422241a0 0x80bed1fb1422241a 0xeffd1ff1c623c7ff 0xeeffd1ff1c623c7f

def z209 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x1e1e1c7e781cf800 0xd1e1e1c7e781cf80

def z210 : W := mkw 0x0960060025401400 0x0096006002540140 0x7fe00e007fc03c0d 0xf7fe00e007fc03c0

def z211 : W := mkw 0x1616385a58fdfcdd 0x41616385a58fdfcd 0xfe1e1c7e79fffcfe 0xffe1e1c7e79fffcf

def z212 : W := mkw 0x0000000200040841 0x0000000020004084 0xe0030e0f803f3cff 0xbe0030e0f803f3cf

def z213 : W := mkw 0x100000120804e8c5 0x0100000120804e8c 0x200000000000f8c0 0x0200000000000f8c

def z214 : W := mkw 0x0000200000890008 0x0000020000089000 0x0062e00001dc0000 0x90062e00001dc000

def z215 : W := mkw 0x4004200077bb0008 0x04004200077bb000 0x5063e0007fff000b 0xb5063e0007fff000

def z216 : W := mkw 0x0616185840204080 0x0061618584020408 0xae1e1c7e4020c0ce 0xeae1e1c7e4020c0c

def z217 : W := mkw 0x128d18fb4a26e9e5 0x8128d18fb4a26e9e 0xe19d1fffc623ffff 0x6e19d1fffc623fff

def z218 : W := mkw 0x849b80e900000000 0x0849b80e90000000 0x001c007000000000 0x0001c00700000000

def z219 : W := mkw 0x169f18fb5a36e9e5 0x8169f18fb5a36e9e 0xbf9e1dfe7e3cfbce 0xfbf9e1dfe7e3cfbc

def z220 : W := mkw 0x296007002d40b606 0x0296007002d40b60 0x71e003807fc0ff09 0x171e003807fc0ff0

def z221 : W := mkw 0x008d200042ab0008 0x0008d200042ab000 0x41ffe00047ff000b 0xf41ffe00047ff000

def z222 : W := mkw 0x49c9a000278b0008 0x049c9a000278b000 0x41e3e00007ff000b 0xb41e3e00007ff000

def z223 : W := mkw 0x2bed1f006f62b606 0x02bed1f006f62b60 0x7ffd1f807fe3ff0f 0xf7ffd1f807fe3ff0

def z224 : W := mkw 0x8ddbc0ed80000000 0x08ddbc0ed8000000 0x8fffe07f80000003 0xe8fffe07f8000000

def z225 : W := mkw 0x4944200077bb0008 0x04944200077bb000 0x5fe000007fff0009 0xf5fe000007fff000

def z226 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x9e1e107e783cc0c2 0x49e1e107e783cc0c

def z227 : W := mkw 0x449fa00052bb0008 0x0449fa00052bb000 0x407fe00001ff000b 0xb407fe00001ff000

def z228 : W := mkw 0x00246616c2ef5df9 0xc00246616c2ef5df 0xe063ee0fc7ffffff 0xbe063ee0fc7fffff

def z229 : W := mkw 0x028d18b14a22e1a4 0x8028d18b14a22e1a 0xff9d1ff1fe23ffff 0xfff9d1ff1fe23fff

def z230 : W := mkw 0x04366606d0fd1c59 0x404366606d0fd1c5 0xfe7fee0ff9ff3cff 0xffe7fee0ff9ff3cf

def z231 : W := mkw 0x0020460480000000 0x0002046048000000 0x0062ec0e00000000 0x80062ec0e0000000

def z232 : W := mkw 0xcffbffedb5990008 0x0cffbffedb599000 0x9fffffffb9dc0007 0xf9fffffffb9dc000

def z233 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0000201800004f4 0x0a0000201800004f

def z234 : W := mkw 0x3f721f4a3d54be47 0x03f721f4a3d54be4 0x1e620c0e39dc3800 0x91e620c0e39dc380

def z235 : W := mkw 0x82205fed80000000 0x082205fed8000000 0x8063ffff80000007 0xa8063ffff8000000

def z236 : W := mkw 0x020418104820e084 0x0020418104820e08 0xbe1c1c707820f8ce 0xfbe1c1c707820f8c

def z237 : W := mkw 0x82ad5ffdc22241a0 0x882ad5ffdc22241a 0xe19d1fffc623c7ff 0x6e19d1fffc623c7f

def z238 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0xffffe201ffff04ff 0xfffffe201ffff04f

def z239 : W := mkw 0x008900a100000000 0x0008900a10000000 0x019c11f000000000 0x4019c11f00000000

def z240 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x5fe00f803fc03f01 0x95fe00f803fc03f0

def z241 : W := mkw 0x4d56a00077bb0008 0x04d56a00077bb000 0x5e62e0007fff0008 0x95e62e0007fff000

def z242 : W := mkw 0x2b601f022d44be47 0x02b601f022d44be4 0xffe21f8e7ffcffcf 0xfffe21f8e7ffcffc

def z243 : W := mkw 0x0940200025890008 0x0094020002589000 0x5fe3e0007fff000b 0xf5fe3e0007fff000

def z244 : W := mkw 0x4004000077320000 0x0400400007732000 0x100000007e000000 0x0100000007e00000

def z245 : W := mkw 0x0d52800000000000 0x00d5280000000000 0x0e62e00000000000 0x80e62e0000000000

def z246 : W := mkw 0x84bbe6ef80cd1c59 0x484bbe6ef80cd1c5 0xe07fee7f81ff3cff 0xbe07fee7f81ff3cf

def z247 : W := mkw 0x0000000000000000 0x0000000000000000 0x80010001802300f2 0x080010001802300f

def z248 : W := mkw 0x1004201258fdfcdd 0x41004201258fdfcd 0x7000000079fffcf8 0x17000000079fffcf

def z249 : W := mkw 0x000000b1000041a0 0x8000000b1000041a 0xe00113f18023c7ff 0x2e00113f18023c7f

def z250 : W := mkw 0x2b601f002d00a206 0x02b601f002d00a20 0x1fe01f807e00c305 0xe1fe01f807e00c30

def z251 : W := mkw 0x49c9800027020000 0x049c980002702000 0x0180000006000000 0x0018000000600000

def z252 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x801d0071802300f2 0x0801d0071802300f

def z253 : W := mkw 0x449f800052320000 0x0449f80005232000 0x001c000000000000 0x0001c00000000000

def z254 : W := mkw 0x000400b1422241a0 0x8000400b1422241a 0xe00013f1c623c7fc 0x0e00013f1c623c7f

def z255 : W := mkw 0x8fdf99f9422241a0 0x88fdf99f9422241a 0xef9d13f1c623c7ff 0x6ef9d13f1c623c7f

def z256 : W := mkw 0x8f72dfed80000000 0x08f72dfed8000000 0x8e62ffff80000004 0x88e62ffff8000000

def z257 : W := mkw 0x00a946a580000000 0x000a946a58000000 0x81ffffff80000007 0xe81ffffff8000000

def z258 : W := mkw 0x0004001040204080 0x0000400104020408 0x001c10704000c000 0x4001c10704000c00

def z259 : W := mkw 0x29606704a5c9161a 0x429606704a5c9161 0x41e1e38187c30731 0x041e1e38187c3073

def z260 : W := mkw 0x020018000800a004 0x0020018000800a00 0x7f801f807e00ff0d 0xf7f801f807e00ff0

def z261 : W := mkw 0x0b40190000000000 0x00b4019000000000 0x0f80118000000000 0x40f8011800000000

def z262 : W := mkw 0x4004200277ff1c59 0x44004200277ff1c5 0x700000007fff3cf8 0x1700000007fff3cf

def z263 : W := mkw 0x09606606a5cd1c59 0x409606606a5cd1c5 0xffe3ee0fffff3cff 0xfffe3ee0fffff3cf

def z264 : W := mkw 0x2b4019002d00a206 0x02b4019002d00a20 0x3f801d807e00fb0c 0xf3f801d807e00fb0

def z265 : W := mkw 0x8ffbdfed82020120 0x88ffbdfed8202012 0xcfffffff86030737 0xecfffffff8603073

def z266 : W := mkw 0xcffffffdf7bb41a8 0x8cffffffdf7bb41a 0xffffffffffffc7ff 0xfffffffffffffc7f

def z267 : W := mkw 0x2b601fb12d40f7a6 0x82b601fb12d40f7a 0xffe01ff1ffc0fffd 0xfffe01ff1ffc0fff

def z268 : W := mkw 0x29606706a5cd1e5b 0x429606706a5cd1e5 0xe1e3ef8f87ff3fff 0xbe1e3ef8f87ff3ff

def z269 : W := mkw 0x4fdfb84877bb0008 0x04fdfb84877bb000 0xdffffc7e7fff000f 0xfdffffc7e7fff000

def z270 : W := mkw 0x2940010025000202 0x0294001002500020 0x0180018006000300 0x0018001800600030

def z271 : W := mkw 0x00ad46b5c22241a0 0x800ad46b5c22241a 0xe1ffffffc623c7ff 0xee1ffffffc623c7f

def z272 : W := mkw 0x82207fef80cd1c59 0x482207fef80cd1c5 0xe063ffff81ff3cff 0xbe063ffff81ff3cf

def z273 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xe01d0271802304ff 0x2e01d0271802304f

def z274 : W := mkw 0x0dfbc60480000000 0x00dfbc6048000000 0x8fffee0f80000007 0xe8fffee0f8000000

def z275 : W := mkw 0x2b607f06adcdbe5f 0x42b607f06adcdbe5 0xfe63ee0fb9ff3cff 0xbfe63ee0fb9ff3cf

def z276 : W := mkw 0x9f72df4e9814a845 0x09f72df4e9814a84 0x1e62ec0e381c3800 0x91e62ec0e381c380

def z277 : W := mkw 0x1612185a0804e8c5 0x01612185a0804e8c 0xae1e1c7e0000f8c6 0xeae1e1c7e0000f8c

def z278 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x1ffee0007fdc0000 0xd1ffee0007fdc000

def z279 : W := mkw 0x449fa00052bb0008 0x0449fa00052bb000 0x419fe000463f000b 0x6419fe000463f000

def z280 : W := mkw 0x000000b1000041a0 0x8000000b1000041a 0xa00013f18000c7f4 0x0a00013f18000c7f

def z281 : W := mkw 0x49cda0b167ab41a8 0x849cda0b167ab41a 0xe1fdf3f1c7e3c7ff 0x6e1fdf3f1c7e3c7f

def z282 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x0ffefdfe00000000 0xc0ffefdfe0000000

def z283 : W := mkw 0x0000000200040841 0x0000000020004084 0xa0000c0e000038c4 0x0a0000c0e000038c

def z284 : W := mkw 0x4ddba000278b0008 0x04ddba000278b000 0x4fffe00007c30003 0xe4fffe00007c3000

def z285 : W := mkw 0x0000000025000000 0x0000000002500000 0x500000007fc00008 0x1500000007fc0000

def z286 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0x5ffff1f07fffc30b 0xf5ffff1f07fffc30

def z287 : W := mkw 0x06325e4c80000000 0x006325e4c8000000 0x8e7ffe7f80000007 0xe8e7ffe7f8000000

def z288 : W := mkw 0x0000200000890008 0x0000020000089000 0x0003e000003f0002 0x00003e000003f000

def z289 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xefffffffc600c70f 0xeefffffffc600c70

def z290 : W := mkw 0x161618585830e084 0x0161618585830e08 0xbe1c10707820c0ce 0x6be1c10707820c0c

def z291 : W := mkw 0x82205f4c80000000 0x082205f4c8000000 0x00000c0e00000000 0x000000c0e0000000

def z292 : W := mkw 0x89e9c7a582020120 0x889e9c7a58202012 0x41e1e38186030731 0x041e1e3818603073

def z293 : W := mkw 0xcfdf99e977320000 0x0cfdf99e97732000 0x1f9c11f07e000000 0x41f9c11f07e00000

def z294 : W := mkw 0x96365fffd834e8c5 0x096365fffd834e8c 0xbe1e1ffff83cf8ce 0xfbe1e1ffff83cf8c

def z295 : W := mkw 0x00ad66b5c2eb55b8 0xc00ad66b5c2eb55b 0xe1fdf3f1c7e3c7ff 0x6e1fdf3f1c7e3c7f

def z296 : W := mkw 0x0020460480401410 0x4002046048040141 0x0000020180000430 0x0000002018000043

def z297 : W := mkw 0xafdb99e92d00a206 0x0afdb99e92d00a20 0x1f9c11f07e00c300 0x41f9c11f07e00c30

def z298 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xfe1f1e7ff83ffcff 0xffe1f1e7ff83ffcf

def z299 : W := mkw 0x2b4019002d00a206 0x02b4019002d00a20 0x7f8013807e00c70d 0x67f8013807e00c70

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0x801c107000000006 0x6801c10700000000

def z301 : W := mkw 0x4416200077bb0008 0x04416200077bb000 0x5e1e00007fff000a 0xf5e1e00007fff000

def z302 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xe01d0071c623c7fa 0x0e01d0071c623c7f

def z303 : W := mkw 0x00ad06b1426255a0 0x800ad06b1426255a 0xe1fd1ff1c7e3ffff 0xfe1fd1ff1c7e3fff

def z304 : W := mkw 0x8ffb9fe900000000 0x08ffb9fe90000000 0x0ffc1ff000000005 0xe0ffc1ff00000000

def z305 : W := mkw 0x0412000010100000 0x0041200001010000 0x1e020000381c0000 0x91e020000381c000

def z306 : W := mkw 0xaf72df4cad40b606 0x0af72df4cad40b60 0x1e62ec0e39c03800 0x91e62ec0e39c0380

def z307 : W := mkw 0x8fdbd9ed80000000 0x08fdbd9ed8000000 0x8f9ff1ff80000002 0x48f9ff1ff8000000

def z308 : W := mkw 0x0000000000000000 0x0000000000000000 0xe1811381c623c7ff 0x6e1811381c623c7f

def z309 : W := mkw 0x4ddf80b1773241a0 0x84ddf80b1773241a 0xff9d13f1fe23c7ff 0x6ff9d13f1fe23c7f

def z310 : W := mkw 0x8ffbdffd800041a0 0x88ffbdffd800041a 0xafffffff8000c7f7 0xeafffffff8000c7f

def z311 : W := mkw 0x0000000200040841 0x0000000020004084 0x00020c0e001c3800 0x900020c0e001c380

def z312 : W := mkw 0x4dffe6b7f7ff5df9 0xc4dffe6b7f7ff5df 0xffffffffffffffff 0xffffffffffffffff

def z313 : W := mkw 0x2b4019002d00a206 0x02b4019002d00a20 0x1e00000038000000 0x01e0000003800000

def z314 : W := mkw 0x0ddba00000890008 0x00ddba0000089000 0x4fffe00001ff000b 0xf4fffe00001ff000

def z315 : W := mkw 0x020018000800a004 0x0020018000800a00 0x1e0010007800c000 0x41e0010007800c00

def z316 : W := mkw 0x4ddfa01077bb4088 0x04ddfa01077bb408 0xfffff0707fffc0cf 0xffffff0707fffc0c

def z317 : W := mkw 0x4ddf80b1773241a0 0x84ddf80b1773241a 0x1f9c11f07e00c300 0x41f9c11f07e00c30

def z318 : W := mkw 0x8fdf99f9422241a0 0x88fdf99f9422241a 0x0f9c11f04600c300 0x40f9c11f04600c30

def z319 : W := mkw 0x1612184a1814a845 0x01612184a1814a84 0xbe020c0e383c38ce 0xbbe020c0e383c38c

def z320 : W := mkw 0x4000200035990008 0x0400020003599000 0x1000000039dc0000 0x11000000039dc000

def z321 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x1fe01f8039c03805 0xf1fe01f8039c0380

def z322 : W := mkw 0x8ffbdfed8800a004 0x08ffbdfed8800a00 0xbffffffff800f80f 0xfbffffffff800f80

def z323 : W := mkw 0x00a966a782cf1d79 0xc00a966a782cf1d7 0xe1e3ef8f87ff3fff 0xbe1e3ef8f87ff3ff

def z324 : W := mkw 0x0000200000890008 0x0000020000089000 0xe063e20181ff04ff 0xbe063e20181ff04f

def z325 : W := mkw 0x4ddfa01077bb41a8 0x84ddfa01077bb41a 0x7fffe0007fffc7fb 0xf7fffe0007fffc7f

def z326 : W := mkw 0x12205e5e8844fcd5 0x412205e5e8844fcd 0xa0001e7f8000fcf4 0x0a0001e7f8000fcf

def z327 : W := mkw 0x9ffbdfef9814a845 0x09ffbdfef9814a84 0x9fffffffb81c3807 0xf9fffffffb81c380

def z328 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xff9e1ffe7e3cffcf 0xfff9e1ffe7e3cffc

def z329 : W := mkw 0x0020460480000000 0x0002046048000000 0xe063ee0f802304ff 0xae063ee0f802304f

def z330 : W := mkw 0x0b4018002d00a004 0x00b4018002d00a00 0x7fe01c007fc0f80d 0xf7fe01c007fc0f80

def z331 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000000002304f8 0x060000000002304f

def z332 : W := mkw 0x000000b1000041a0 0x8000000b1000041a 0x000011f00000c300 0x0000011f00000c30

def z333 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x619c11f04623c7f8 0x4619c11f04623c7f

def z334 : W := mkw 0x0960070000000000 0x0096007000000000 0x01e0038000000001 0x001e003800000000

def z335 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x001c007000000000 0x0001c00700000000

def z336 : W := mkw 0x8fdb99e900000000 0x08fdb99e90000000 0x8f9e1dfe00000006 0xe8f9e1dfe0000000

def z337 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x619c13f04600c70d 0x6619c13f04600c70

def z338 : W := mkw 0x6fff9f007f72b606 0x06fff9f007f72b60 0x7ffc1f807fc0ff0d 0xf7ffc1f807fc0ff0

def z339 : W := mkw 0x40246606f7ff1c59 0x440246606f7ff1c5 0xf063ee0fffff3cff 0xbf063ee0fffff3cf

def z340 : W := mkw 0x00040012402448c1 0x000040012402448c 0xa01e1c7e403cf8ce 0xfa01e1c7e403cf8c

def z341 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0x9fffffffb9c03807 0xf9fffffffb9c0380

def z342 : W := mkw 0x02201f0000000000 0x002201f000000000 0x00001f8000000004 0x000001f800000000

def z343 : W := mkw 0xa9e9c7a5a5401602 0x0a9e9c7a5a540160 0x41e1e38187c00701 0x041e1e38187c0070

def z344 : W := mkw 0x969fd8ffd834e8c5 0x0969fd8ffd834e8c 0xbe1ffc7ff83cf8ce 0xfbe1ffc7ff83cf8c

def z345 : W := mkw 0x0000000002020120 0x8000000000202012 0x4000000006030730 0x0400000000603073

def z346 : W := mkw 0x8f72df4c80000000 0x08f72df4c8000000 0x0fe2ff8e00000005 0xe0fe2ff8e0000000

def z347 : W := mkw 0x49e9e606a7cf1c59 0x449e9e606a7cf1c5 0xe1e3ee0f87ff3cff 0xbe1e3ee0f87ff3cf

def z348 : W := mkw 0x2b607f04adc9b61e 0x42b607f04adc9b61 0x7fe1ff81ffc3ff3d 0xf7fe1ff81ffc3ff3

def z349 : W := mkw 0x5fdfb84a7fbfa84d 0x05fdfb84a7fbfa84 0x5fffec0e7fff380b 0xf5fffec0e7fff380

def z350 : W := mkw 0x6dffa70077fb160a 0x06dffa70077fb160 0x5fffe3807fff070b 0xf5fffe3807fff070

def z351 : W := mkw 0x44bfe606d2ff1c59 0x444bfe606d2ff1c5 0xe07fee0f81ff3cff 0xbe07fee0f81ff3cf

def z352 : W := mkw 0x2bcd19b16f22e3a6 0x82bcd19b16f22e3a 0xff9d13f1fe23c7ff 0x6ff9d13f1fe23c7f

def z353 : W := mkw 0x0ddf800042220000 0x00ddf80004222000 0x4fffe0004623000b 0xe4fffe0004623000

def z354 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x61810381c623c7f9 0x061810381c623c7f

def z355 : W := mkw 0x294000002d40b606 0x0294000002d40b60 0x7fe000007fc0ff09 0xf7fe000007fc0ff0

def z356 : W := mkw 0x120018fb0804e9e5 0x8120018fb0804e9e 0xa0001fff8000fff4 0x0a0001fff8000fff

def z357 : W := mkw 0xab605fedad40b606 0x0ab605fedad40b60 0xffe01fffffc0ff0d 0xfffe01fffffc0ff0

def z358 : W := mkw 0x220018002d40b606 0x0220018002d40b60 0x7e001c007fc0ff0c 0xf7e001c007fc0ff0

def z359 : W := mkw 0x0004001040204080 0x0000400104020408 0xe01d1271c023c4ff 0x6e01d1271c023c4f

def z360 : W := mkw 0x06327e4e80cd1c59 0x406327e4e80cd1c5 0xee7ffe7f81ff3cff 0xfee7ffe7f81ff3cf

def z361 : W := mkw 0x89c981a100000000 0x089c981a10000000 0x0180018000000000 0x0018001800000000

def z362 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x419d11f04623c30b 0x6419d11f04623c30

def z363 : W := mkw 0x449fa00077bb0008 0x0449fa00077bb000 0x501fe0007fff000a 0x1501fe0007fff000

def z364 : W := mkw 0x008900b1000041a0 0x8008900b1000041a 0xa19d13f18000c7f7 0x6a19d13f18000c7f

def z365 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x9e1e0c7e383c38c2 0x99e1e0c7e383c38c

def z366 : W := mkw 0xcf72ff4cb5990008 0x0cf72ff4cb599000 0x1e62ec0e39dc0000 0x91e62ec0e39dc000

def z367 : W := mkw 0x1416005850304080 0x0141600585030408 0x001c007000000000 0x0001c00700000000

def z368 : W := mkw 0x008d60b7c2af49f9 0xc008d60b7c2af49f 0xe19ff3ffc63fc7ff 0x6e19ff3ffc63fc7f

def z369 : W := mkw 0x0ddb80a100000000 0x00ddb80a10000000 0x8ffff3f180000007 0xe8ffff3f18000000

def z370 : W := mkw 0x8fffdfedd0300000 0x08fffdfedd030000 0x9ffffffff83c000f 0xf9ffffffff83c000

def z371 : W := mkw 0x0020460680441c51 0x40020460680441c5 0xa0020e0f803c3cfe 0xba0020e0f803c3cf

def z372 : W := mkw 0x0020460680441c51 0x40020460680441c5 0xe0600e0f81c03cfd 0xbe0600e0f81c03cf

def z373 : W := mkw 0x008d00b3422649e1 0x8008d00b3422649e 0xe19f1fffc63fffff 0xfe19f1fffc63ffff

def z374 : W := mkw 0x849be0ef808d0859 0x4849be0ef808d085 0x801fe07f803f00f2 0x0801fe07f803f00f

def z375 : W := mkw 0x0020660480c91418 0x40020660480c9141 0x6061ee0181c33c3d 0xb6061ee0181c33c3

def z376 : W := mkw 0x0020660480c91418 0x40020660480c9141 0x4063e20181ff043b 0xb4063e20181ff043

def z377 : W := mkw 0x2b641f106d60f686 0x02b641f106d60f68 0xfffc1ff07fe0ffcf 0xffffc1ff07fe0ffc

def z378 : W := mkw 0x00040010422241a0 0x800040010422241a 0xe01c10704623c7fe 0x6e01c10704623c7f

def z379 : W := mkw 0x0000200200cd1c59 0x40000200200cd1c5 0x6063e00001ff3cfb 0xb6063e00001ff3cf

def z380 : W := mkw 0x5fdf985a7f36e8c5 0x05fdf985a7f36e8c 0xbf9e1c7e7e3cf8ce 0xfbf9e1c7e7e3cf8c

def z381 : W := mkw 0x16327e4e98ddbc5d 0x416327e4e98ddbc5 0x1e62ec0e39dc3800 0x91e62ec0e39dc380

def z382 : W := mkw 0x008900a100000000 0x0008900a10000000 0x801d007180000002 0x0801d00718000000

def z383 : W := mkw 0x8b605fed80000000 0x08b605fed8000000 0x8fe01fff80000005 0xe8fe01fff8000000

def z384 : W := mkw 0x141600125834e8c5 0x0141600125834e8c 0x3e1e0000783cf8ca 0xf3e1e0000783cf8c

def z385 : W := mkw 0x2bcd19b16f22e3a6 0x82bcd19b16f22e3a 0x1f9c11f07e00c300 0x41f9c11f07e00c30

def z386 : W := mkw 0x0f721f4800000000 0x00f721f480000000 0x8ffe1ffe00000007 0xe8ffe1ffe0000000

def z387 : W := mkw 0x8be9dfed80000000 0x08be9dfed8000000 0x81e1ffff80000005 0x081e1ffff8000000

def z388 : W := mkw 0x8f52994800000000 0x08f5299480000000 0x0e00000000000000 0x00e0000000000000

def z389 : W := mkw 0x2960070025401602 0x0296007002540160 0x61e0138047c0c70d 0x661e0138047c0c70

def z390 : W := mkw 0x0be91fa100000000 0x00be91fa10000000 0x8ffd1ff180000007 0xe8ffd1ff18000000

def z391 : W := mkw 0x0089000000000000 0x0008900000000000 0x019d000000000003 0x6019d00000000000

def z392 : W := mkw 0x1000005a000448c1 0x01000005a000448c 0x8000007e000000c0 0x08000007e000000c

def z393 : W := mkw 0xbfffdffffd74fec7 0x0bfffdffffd74fec 0xfffffffffffcffcf 0xffffffffffffcffc

def z394 : W := mkw 0x1200185a0804e8c5 0x01200185a0804e8c 0xa0021c7e003cf8ce 0xba0021c7e003cf8c

def z395 : W := mkw 0x0020060200441c41 0x00020060200441c4 0xe0620e0e01fc3ccf 0xbe0620e0e01fc3cc

def z396 : W := mkw 0x0020660480c91418 0x40020660480c9141 0xc063ee0f81c30437 0xac063ee0f81c3043

def z397 : W := mkw 0x0000200000c91418 0x40000200000c9141 0x4000000001c30430 0x04000000001c3043

def z398 : W := mkw 0x8ffbdfef80441c51 0x48ffbdfef80441c5 0xafffffff80003cf7 0xeafffffff80003cf

def z399 : W := mkw 0x008d20b342ef5df9 0xc008d20b342ef5df 0xe19d13f1c7ffffff 0x7e19d13f1c7fffff

def z400 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x3e601c0079c0f80c 0xf3e601c0079c0f80

def z401 : W := mkw 0x00000010000041a0 0x800000010000041a 0x200000000000c7f0 0x0200000000000c7f

def z402 : W := mkw 0x2f721f482d40b606 0x02f721f482d40b60 0xfffe1ffe7fc0ff0f 0xffffe1ffe7fc0ff0

def z403 : W := mkw 0x36361f5a5874fec7 0x036361f5a5874fec 0xbe1e1ffe783cffce 0xfbe1e1ffe783cffc

def z404 : W := mkw 0x84bbc6ed80000000 0x084bbc6ed8000000 0x807fee7f80000007 0xa807fee7f8000000

def z405 : W := mkw 0x2960070025401602 0x0296007002540160 0x0060000001c00000 0x00060000001c0000

def z406 : W := mkw 0x449fa0b152bb41a8 0x8449fa0b152bb41a 0x801fe071803f00f2 0x0801fe071803f00f

def z407 : W := mkw 0x3b601f5a2d44fec7 0x03b601f5a2d44fec 0xffe01ffe7fc0ffcd 0xfffe01ffe7fc0ffc

def z408 : W := mkw 0x0000000000000000 0x0000000000000000 0x4180038006000701 0x0418003800600070

def z409 : W := mkw 0x5fdfb8fb7fbfe9ed 0x85fdfb8fb7fbfe9e 0xffffffffffffffff 0xffffffffffffffff

def z410 : W := mkw 0x6f72bf003dd9b60e 0x06f72bf003dd9b60 0x7fe2ff807fdcff0d 0xf7fe2ff807fdcff0

def z411 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x3e020c0e783cf8c8 0x93e020c0e783cf8c

def z412 : W := mkw 0x0ddb800025000000 0x00ddb80002500000 0x5fffe0007fc0000b 0xf5fffe0007fc0000

def z413 : W := mkw 0x9fdf99f95830e084 0x09fdf99f95830e08 0x1f9c11f07800c000 0x41f9c11f07800c00

def z414 : W := mkw 0x2b601f0025401602 0x02b601f002540160 0x4fe01f8007c00705 0xe4fe01f8007c0070

def z415 : W := mkw 0x1616385a58bde8cd 0x01616385a58bde8c 0xfe7ffc7e79fff8cf 0xffe7ffc7e79fff8c

def z416 : W := mkw 0x4ddf800077320000 0x04ddf80007732000 0x1fffe0007e000003 0xe1fffe0007e00000

def z417 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xc19d0071c62300fb 0x6c19d0071c62300f

def z418 : W := mkw 0x22205f068844be57 0x422205f068844be5 0xa0001f8f8000fff4 0x0a0001f8f8000fff

def z419 : W := mkw 0x161618585830e084 0x0161618585830e08 0x3e1c1c707800f80c 0xf3e1c1c707800f80

def z420 : W := mkw 0x0b601f0000401400 0x00b601f000040140 0x6fe01f8001c03c0d 0xf6fe01f8001c03c0

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0x600000004600c708 0x0600000004600c70

def z422 : W := mkw 0x1204185a4824e8c5 0x01204185a4824e8c 0xa01c1c7e4020f8ce 0x6a01c1c7e4020f8c

def z423 : W := mkw 0x8dfbc7ed80000000 0x08dfbc7ed8000000 0x81ffe3ff80000003 0x081ffe3ff8000000

def z424 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xa01d1071c023c0fe 0x6a01d1071c023c0f

def z425 : W := mkw 0x4d52800035100000 0x04d5280003510000 0x1e00000038000000 0x01e0000003800000

def z426 : W := mkw 0x0000200200cd1c59 0x40000200200cd1c5 0xe001020181ff3cff 0x3e001020181ff3cf

def z427 : W := mkw 0x149f00fb523649e1 0x8149f00fb523649e 0xe19f13ffc63fc7ff 0x6e19f13ffc63fc7f

def z428 : W := mkw 0x4dffe606f7ff1c59 0x44dffe606f7ff1c5 0x5fffec0e7fff380b 0xf5fffec0e7fff380

def z429 : W := mkw 0x22201f000840b606 0x022201f000840b60 0x60601f8001c0ff0d 0xb60601f8001c0ff0

def z430 : W := mkw 0x208d00b16f62f7a6 0x8208d00b16f62f7a 0xf19d13f1ffe3ffff 0x7f19d13f1ffe3fff

def z431 : W := mkw 0x0612184a00040841 0x00612184a0004084 0xae1e1c7e003c38ce 0xfae1e1c7e003c38c

def z432 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x6fe01f804600c70d 0xe6fe01f804600c70

def z433 : W := mkw 0x049f00b1523241a0 0x8049f00b1523241a 0xff9f13f1fe3fc7ff 0xfff9f13f1fe3fc7f

def z434 : W := mkw 0xdfffffffffbfe8cd 0x0dfffffffffbfe8c 0xfffffffffffff8cf 0xffffffffffffff8c

def z435 : W := mkw 0x89e9c7a580000000 0x089e9c7a58000000 0x81fdf3f180000007 0x681fdf3f18000000

def z436 : W := mkw 0x0020460680441c51 0x40020460680441c5 0xe0010e0f80233cff 0x2e0010e0f80233cf

def z437 : W := mkw 0x8ffbdfeda5000000 0x08ffbdfeda500000 0xdfffffffffc0000f 0xfdfffffffffc0000

def z438 : W := mkw 0x0020660480c91418 0x40020660480c9141 0x0060e00001c00000 0x00060e00001c0000

def z439 : W := mkw 0x4ddf800077320000 0x04ddf80007732000 0x1f9e00007e3c000a 0xf1f9e00007e3c000

def z440 : W := mkw 0x449fa00052bb0008 0x0449fa00052bb000 0x1e1fe000783f000a 0xf1e1fe000783f000

def z441 : W := mkw 0x8fdb99e900000000 0x08fdb99e90000000 0x8f9d13f180000007 0x68f9d13f18000000

def z442 : W := mkw 0x49c9a000278b0008 0x049c9a000278b000 0x5fe1e0007fc30009 0xf5fe1e0007fc3000

def z443 : W := mkw 0x0020460680040841 0x0002046068004084 0xa063ee0f803c38cf 0xba063ee0f803c38c

def z444 : W := mkw 0x1200185a0804e8c5 0x01200185a0804e8c 0xbe001c7e7800f8cc 0xfbe001c7e7800f8c

def z445 : W := mkw 0x0000000200040841 0x0000000020004084 0x20000000003c38c8 0x120000000003c38c

def z446 : W := mkw 0x0000600480890018 0x4000060048089001 0x0001e00180030030 0x00001e0018003003

def z447 : W := mkw 0x4ddf800077320000 0x04ddf80007732000 0x5ffc00007fc00009 0xf5ffc00007fc0000

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x0063e00000000003 0xa0063e0000000000

def z449 : W := mkw 0x008900a100000000 0x0008900a10000000 0x0181038180000001 0x0018103818000000

def z450 : W := mkw 0x0416001050304080 0x0041600105030408 0xbe1e1070783cc0ce 0xfbe1e1070783cc0c

def z451 : W := mkw 0x108d00b35a36e9e5 0x8108d00b35a36e9e 0xf19d13f1fe3fffff 0x7f19d13f1fe3ffff

def z452 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x0ffdf3f180000001 0x40ffdf3f18000000

def z453 : W := mkw 0x4fdfb8007fbba00c 0x04fdfb8007fbba00 0x7ffffc007ffff80f 0xf7ffffc007ffff80

def z454 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x61e01f8007c0ff05 0x061e01f8007c0ff0

def z455 : W := mkw 0x100400125834e8c5 0x0100400125834e8c 0xb0020c0e783cf8ce 0xbb0020c0e783cf8c

def z456 : W := mkw 0x4ddfe006f7bf0859 0x44ddfe006f7bf085 0xdfffe00fffff00fb 0xfdfffe00fffff00f

def z457 : W := mkw 0x0020460480000000 0x0002046048000000 0x80000e0f80000004 0x080000e0f8000000

def z458 : W := mkw 0x16327e4e98ddbc5d 0x416327e4e98ddbc5 0xfe63ee0fb9ff3cff 0xbfe63ee0fb9ff3cf

def z459 : W := mkw 0x0b607f0680cd1c59 0x40b607f0680cd1c5 0xefe3ff8f81ff3cff 0xfefe3ff8f81ff3cf

def z460 : W := mkw 0x0000000200040841 0x0000000020004084 0x8002000e003c00c2 0x08002000e003c00c

def z461 : W := mkw 0x4ddfa00277bf0849 0x04ddfa00277bf084 0xffffec0e7fff38cf 0xfffffec0e7fff38c

def z462 : W := mkw 0x02201e000840b404 0x002201e000840b40 0x7e601e0079c0fc0d 0xf7e601e0079c0fc0

def z463 : W := mkw 0x0000000000000000 0x0000000000000000 0x4180000046000009 0x6418000004600000

def z464 : W := mkw 0xaf72df4cad40b606 0x0af72df4cad40b60 0x7fe2ff8e7fc0ff0d 0xf7fe2ff8e7fc0ff0

def z465 : W := mkw 0x86bbdfed80000000 0x086bbdfed8000000 0x801fffff80000006 0x0801fffff8000000

def z466 : W := mkw 0x22ad1fb14a62f7a6 0x822ad1fb14a62f7a 0xe19d1ff1c623ffff 0x6e19d1ff1c623fff

def z467 : W := mkw 0x0000200000890008 0x0000020000089000 0x4061e00001c30001 0x04061e00001c3000

def z468 : W := mkw 0x5fdf98587f32e084 0x05fdf98587f32e08 0x1f9c10707e00c000 0x41f9c10707e00c00

def z469 : W := mkw 0x9ffbdfff8804e8c5 0x09ffbdfff8804e8c 0xafffffff8000f8c7 0xeafffffff8000f8c

def z470 : W := mkw 0x6fdf99007f32a206 0x06fdf99007f32a20 0x1f9c11807e00c300 0x41f9c11807e00c30

def z471 : W := mkw 0x0940000025000000 0x0094000002500000 0x41e0000007c00001 0x041e0000007c0000

def z472 : W := mkw 0xabe9dfa5ad40b606 0x0abe9dfa5ad40b60 0x7fe1ff81ffc0ff0d 0xf7fe1ff81ffc0ff0

def z473 : W := mkw 0x1fdf985a5834e8c5 0x01fdf985a5834e8c 0xbffffc7e783cf8cf 0xfbffffc7e783cf8c

def z474 : W := mkw 0x169f18fb5834e8c5 0x0169f18fb5834e8c 0xbf9f1ffff83cf8cf 0xfbf9f1ffff83cf8c

def z475 : W := mkw 0x0412000000000000 0x0041200000000000 0x0e1e000000000002 0xe0e1e00000000000

def z476 : W := mkw 0x86325fed80000000 0x086325fed8000000 0x8e1e1fff80000006 0xe8e1e1fff8000000

def z477 : W := mkw 0x008900a102020120 0x8008900a10202012 0xc19d13f186030737 0x6c19d13f18603073

def z478 : W := mkw 0x1204185a5834e8c5 0x01204185a5834e8c 0xb0001c7e783cf8cc 0x1b0001c7e783cf8c

def z479 : W := mkw 0x049b800000000000 0x0049b80000000000 0x001fe00000000002 0x0001fe0000000000

def z480 : W := mkw 0x120418125834e8c5 0x0120418125834e8c 0x3e001c00783cf8cc 0xf3e001c00783cf8c

def z481 : W := mkw 0x2bed7fb7efefffff 0xc2bed7fb7efeffff 0xffffffffffffffff 0xffffffffffffffff

def z482 : W := mkw 0x4ddba00035990008 0x04ddba0003599000 0x1fffe00039dc0003 0xf1fffe00039dc000

def z483 : W := mkw 0x0000200200cd1c59 0x40000200200cd1c5 0xe0020c0e01ff3cfe 0xbe0020c0e01ff3cf

def z484 : W := mkw 0x161618fb5834e9e5 0x8161618fb5834e9e 0xbe1e1ffff83cfffe 0xfbe1e1ffff83cfff

def z485 : W := mkw 0x008d0010422241a0 0x8008d0010422241a 0x619d00004623c7fb 0x6619d00004623c7f

def z486 : W := mkw 0x6fffff06ffffbe5f 0x46fffff06ffffbe5 0xffffff8fffffffff 0xfffffff8ffffffff

def z487 : W := mkw 0x0416000250340841 0x0041600025034084 0xbe1e0c0e783c38ce 0xfbe1e0c0e783c38c

def z488 : W := mkw 0x0020460680441c51 0x40020460680441c5 0x00000c0e00003800 0x000000c0e0000380

def z489 : W := mkw 0x9f76df5ed834e8c5 0x09f76df5ed834e8c 0xbe7efc7e783cf8ce 0xfbe7efc7e783cf8c

def z490 : W := mkw 0x200000000840b606 0x0200000000840b60 0x200000000000ff00 0x0200000000000ff0

def z491 : W := mkw 0x8089c0a580000000 0x08089c0a58000000 0x0001e00180000000 0x00001e0018000000

def z492 : W := mkw 0x1616785ed8bde8dd 0x41616785ed8bde8d 0xbe1ffc7ff83ff8fe 0xfbe1ffc7ff83ff8f

def z493 : W := mkw 0x0ddb800000000000 0x00ddb80000000000 0x0f9c000000000000 0x40f9c00000000000

def z494 : W := mkw 0x1616185a503448c1 0x01616185a503448c 0x8e1e1c7e003c00c6 0xe8e1e1c7e003c00c

def z495 : W := mkw 0x16365e5ed874fcd5 0x416365e5ed874fcd 0xbe1e1e7ff83cfcfe 0xfbe1e1e7ff83cfcf

def z496 : W := mkw 0x0000000000000000 0x0000000000000000 0x200013800000c704 0x0200013800000c70

def z497 : W := mkw 0x549fa05a52bf48c9 0x0549fa05a52bf48c 0x801fe07e003f00c2 0x0801fe07e003f00c

def z498 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xa01e1c7e003cf8c6 0x0a01e1c7e003cf8c

def z499 : W := mkw 0x0612184800000000 0x0061218480000000 0x0e020c0e00000000 0x80e020c0e0000000

def z500 : W := mkw 0xc9e9e7a5a78b0008 0x0c9e9e7a5a78b000 0x41e1e38187c30001 0x041e1e38187c3000

def z501 : W := mkw 0x16367e5ed8fdfcdd 0x416367e5ed8fdfcd 0xbe7efc7e79fcf8ce 0xfbe7efc7e79fcf8c

def z502 : W := mkw 0x802047a580000000 0x0802047a58000000 0x0000038180000000 0x0000003818000000

def z503 : W := mkw 0x6f72bf003dd9b60e 0x06f72bf003dd9b60 0x1e62ec0039dc3800 0x91e62ec0039dc380

def z504 : W := mkw 0x061218480800a004 0x0061218480800a00 0xbe1e1c7e7800f80e 0xfbe1e1c7e7800f80

def z505 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0x8063ee0f81dc3807 0xb8063ee0f81dc380

def z506 : W := mkw 0x0000200200cd1c59 0x40000200200cd1c5 0x0000000001dc3800 0x10000000001dc380

def z507 : W := mkw 0xaffb9fe92d40b606 0x0affb9fe92d40b60 0x7ffc1ff07fc0ff0d 0xf7ffc1ff07fc0ff0

def z508 : W := mkw 0x02207e0688cdbc5d 0x402207e0688cdbc5 0xfe63fe0ff9fffcff 0xffe63fe0ff9fffcf

def z509 : W := mkw 0x008d001042224080 0x0008d00104222408 0xe19d10704623c0cf 0x6e19d10704623c0c

def z510 : W := mkw 0x200400106f62f7a6 0x8200400106f62f7a 0x700000007fe3fff8 0x1700000007fe3fff

def z511 : W := mkw 0x1f761f5a5834e8c5 0x01f761f5a5834e8c 0xbffe1ffe783cf8cf 0xfbffe1ffe783cf8c

def z512 : W := mkw 0x8fffdffdc0204080 0x08fffdffdc020408 0xafffffffc020c0cf 0xeafffffffc020c0c

def z513 : W := mkw 0x002066b780cd5df9 0xc002066b780cd5df 0xe063ffff81ffffff 0xbe063ffff81fffff

def z514 : W := mkw 0x008900a102020120 0x8008900a10202012 0x0180018006000300 0x0018001800600030

def z515 : W := mkw 0x2b603f002dc9b60e 0x02b603f002dc9b60 0x7fe3ff807fffff0f 0xf7fe3ff807fffff0

def z516 : W := mkw 0x020018000800a004 0x0020018000800a00 0x1e000c0038003800 0x91e000c003800380

def z517 : W := mkw 0x1612185a1814e8c5 0x01612185a1814e8c 0xbe021c7e381cf8c4 0x9be021c7e381cf8c

def z518 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7e600c007fc0ff08 0x97e600c007fc0ff0

def z519 : W := mkw 0x2b641f106f62f7a6 0x82b641f106f62f7a 0x7fe01f807fe3fffd 0xf7fe01f807fe3fff

def z520 : W := mkw 0x09cd00b1672241a0 0x809cd00b1672241a 0xfffd13f1ffe3c7ff 0xffffd13f1ffe3c7f

def z521 : W := mkw 0x2b4019002d40b606 0x02b4019002d40b60 0x7f8011807fc0ff08 0x57f8011807fc0ff0

def z522 : W := mkw 0x0004201242ef5df9 0xc0004201242ef5df 0x6000000047fffff8 0x16000000047fffff

def z523 : W := mkw 0x2bed1fb16f62f7a6 0x82bed1fb16f62f7a 0x7ffc1ff07fc0ff0d 0xf7ffc1ff07fc0ff0

def z524 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000c000000380c 0xb20000c000000380

def z525 : W := mkw 0x00006006808d0859 0x400006006808d085 0xa003ec0f803f38fe 0xba003ec0f803f38f

def z526 : W := mkw 0x949fc0ffd03448c1 0x0949fc0ffd03448c 0x801fe07f803c00c2 0x0801fe07f803c00c

def z527 : W := mkw 0x3b641f127d74fec7 0x03b641f127d74fec 0x7fe01f807ffcffcd 0xf7fe01f807ffcffc

def z528 : W := mkw 0x82205ffd800041a0 0x882205ffd800041a 0xa0001fff8000c7f4 0x0a0001fff8000c7f

def z529 : W := mkw 0x9fffdfffd03448c1 0x09fffdfffd03448c 0x8fffffff803c00c7 0xe8fffffff803c00c

def z530 : W := mkw 0x4ddba000379b0008 0x04ddba000379b000 0x5fe3e0003fdf0001 0x95fe3e0003fdf000

def z531 : W := mkw 0x000000a100000120 0x8000000a10000012 0x0000038180000730 0x0000003818000073

def z532 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1c1c7e7800f8c4 0x4be1c1c7e7800f8c

def z533 : W := mkw 0x0020660480c91418 0x40020660480c9141 0xe061e20181e304ff 0x2e061e20181e304f

def z534 : W := mkw 0x89e9c7a580000000 0x089e9c7a58000000 0x81e3ef8f80000007 0xa81e3ef8f8000000

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180138000000005 0x6018013800000000

def z536 : W := mkw 0x3f5619587d30e286 0x03f5619587d30e28 0x1f9c11f07e00c300 0x41f9c11f07e00c30

def z537 : W := mkw 0x0000200000890008 0x0000020000089000 0x4000000001ff0008 0x14000000001ff000

def z538 : W := mkw 0x0940000025000000 0x0094000002500000 0x7fe013807fc0c70d 0xf7fe013807fc0c70

def z539 : W := mkw 0x00002002008d0849 0x000002002008d084 0xe063ec0e01ff38cf 0xbe063ec0e01ff38c

def z540 : W := mkw 0x1f56185a7d34e8c5 0x01f56185a7d34e8c 0xfffe1c7e7ffcf8cf 0xffffe1c7e7ffcf8c

def z541 : W := mkw 0x8ffbffed80890008 0x08ffbffed8089000 0xcfffffff81ff000f 0xfcfffffff81ff000

def z542 : W := mkw 0xcfffffeff7ff1c59 0x4cfffffeff7ff1c5 0xffffffffffff3cff 0xfffffffffffff3cf

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0x200010004000c00c 0x6200010004000c00

def z544 : W := mkw 0x49cda00067ab0008 0x049cda00067ab000 0x41fde00047e3000b 0x641fde00047e3000

def z545 : W := mkw 0x0416200050b90008 0x00416200050b9000 0x5e7fe00079ff000b 0xf5e7fe00079ff000

def z546 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x1fe01d807fc0fb00 0xd1fe01d807fc0fb0

def z547 : W := mkw 0xcfffdfedf7320000 0x0cfffdfedf732000 0x9ffffffffe000007 0xe9ffffffffe00000

def z548 : W := mkw 0x1416005a503448c1 0x01416005a503448c 0x9e1e007e783c00ca 0xf9e1e007e783c00c

def z549 : W := mkw 0x00040010422241a0 0x800040010422241a 0x00000000002300f0 0x000000000002300f

def z550 : W := mkw 0x161218481810a004 0x0161218481810a00 0x1e00000038000000 0x01e0000003800000

def z551 : W := mkw 0x0004000040200000 0x0000400004020000 0x001c00004020000a 0x6001c00004020000

def z552 : W := mkw 0x0000001000004080 0x0000000100000408 0xa00010700000c0c4 0x0a00010700000c0c

def z553 : W := mkw 0x1416005a5834e8c5 0x01416005a5834e8c 0xb01e007e783cf8ca 0x1b01e007e783cf8c

def z554 : W := mkw 0x89e9e7a780cd1c59 0x489e9e7a780cd1c5 0xe1e3ef8f81ff3cff 0xbe1e3ef8f81ff3cf

def z555 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fe0000000000001 0xe0fe000000000000

def z556 : W := mkw 0x00a966a582cb1538 0xc00a966a582cb153 0x41e1e38187c30731 0x041e1e38187c3073

def z557 : W := mkw 0x8f72df4c80000000 0x08f72df4c8000000 0x8e63ee0f80000007 0xa8e63ee0f8000000

def z558 : W := mkw 0x09c9800000000000 0x009c980000000000 0x01e1e00000000001 0x001e1e0000000000

def z559 : W := mkw 0x8ffbffef80cd1c59 0x48ffbffef80cd1c5 0x8fffffff81dc3807 0xf8fffffff81dc380

def z560 : W := mkw 0x0200180000000000 0x0020018000000000 0x0e001c0000000004 0xe0e001c000000000

def z561 : W := mkw 0x4ddf800077320000 0x04ddf80007732000 0x5f9d00007e23000b 0x65f9d00007e23000

def z562 : W := mkw 0x161618585830e084 0x0161618585830e08 0x9e1e1c7e7800c006 0xe9e1e1c7e7800c00

def z563 : W := mkw 0x020018000800a004 0x0020018000800a00 0x20001c000000f804 0x020001c000000f80

def z564 : W := mkw 0x0004001040204080 0x0000400104020408 0x801c0070002000c2 0x0801c0070002000c

def z565 : W := mkw 0x5fdfb8587fbbe08c 0x05fdfb8587fbbe08 0x5ffff0707fffc00b 0xf5ffff0707fffc00

def z566 : W := mkw 0x6fdfb9007fbba20e 0x06fdfb9007fbba20 0x5ffff1807fffc30b 0xf5ffff1807fffc30

def z567 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x5fe013807fc0c701 0x45fe013807fc0c70

def z568 : W := mkw 0x049f000052320000 0x0049f00005232000 0x5f9f00007e3f000b 0xf5f9f00007e3f000

def z569 : W := mkw 0x200000002d40b606 0x0200000002d40b60 0x718013807fc0ff0d 0x7718013807fc0ff0

def z570 : W := mkw 0x3fff1ffb7f76ffe7 0x83fff1ffb7f76ffe 0xffff1fffffffffff 0xfffff1ffffffffff

def z571 : W := mkw 0x22201fb10840f7a6 0x822201fb10840f7a 0xa0001ff18000fff4 0x0a0001ff18000fff

def z572 : W := mkw 0x0004000042220000 0x0000400004222000 0x4000000046230008 0x0400000004623000

def z573 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0x6062ee0e01dc3c0d 0xb6062ee0e01dc3c0

def z574 : W := mkw 0x3f761f5a7d74fec7 0x03f761f5a7d74fec 0xbe7e1c7e79fcf8ce 0xfbe7e1c7e79fcf8c

def z575 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x3e1c1070783cf8c8 0x53e1c1070783cf8c

def z576 : W := mkw 0x2b605f04ad40b606 0x02b605f04ad40b60 0xffe3ff8fffc0ff0f 0xfffe3ff8fffc0ff0

def z577 : W := mkw 0x00ad46b7c2665df1 0xc00ad46b7c2665df 0xe19d1fffc623ffff 0x6e19d1fffc623fff

def z578 : W := mkw 0x49c9a0a1278b0128 0x849c9a0a1278b012 0x41e1e38187c30731 0x041e1e38187c3073

def z579 : W := mkw 0x8f72ff4e80cd1c59 0x48f72ff4e80cd1c5 0xee63ee0f81ff3cff 0xbee63ee0f81ff3cf

def z580 : W := mkw 0x5ddfa05a77bf48c9 0x05ddfa05a77bf48c 0xdfffe07e7fff00cb 0xfdfffe07e7fff00c

def z581 : W := mkw 0x8dfbc7a580000000 0x08dfbc7a58000000 0x0fffe38180000003 0xe0fffe3818000000

def z582 : W := mkw 0x1416605ed0bd48d9 0x41416605ed0bd48d 0x801fe07f803f00f2 0x0801fe07f803f00f

def z583 : W := mkw 0x000000b1000041a0 0x8000000b1000041a 0x80000071800000f0 0x080000071800000f

def z584 : W := mkw 0x16361e5a5874fcc5 0x016361e5a5874fcc 0xfe7e1e7e79fcfccf 0xffe7e1e7e79fcfcc

def z585 : W := mkw 0x9fdf99fb5834e8c5 0x09fdf99fb5834e8c 0xbf9e1dfe783cf8ce 0xfbf9e1dfe783cf8c

def z586 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0x4063ec0e01ff380b 0xb4063ec0e01ff380

def z587 : W := mkw 0x8fffffffc2ef5df9 0xc8fffffffc2ef5df 0xefffffffc7ffffff 0xfefffffffc7fffff

def z588 : W := mkw 0x10040012503448c1 0x010040012503448c 0x00000000003c00c0 0x000000000003c00c

def z589 : W := mkw 0x8fffdffdc22241a0 0x88fffdffdc22241a 0x8fffffffc600c307 0xe8fffffffc600c30

def z590 : W := mkw 0x1416005a503448c1 0x01416005a503448c 0xa01e107e403cc0ce 0x6a01e107e403cc0c

def z591 : W := mkw 0x6be9bf002fcbb60e 0x06be9bf002fcbb60 0x7fe1ff807fc3ff0d 0xf7fe1ff807fc3ff0

def z592 : W := mkw 0x2b607f06adcdbe5f 0x42b607f06adcdbe5 0x7fe2ff8e7fdcff0d 0xf7fe2ff8e7fdcff0

def z593 : W := mkw 0x0000400680040851 0x4000040068004085 0x8000000f800000f0 0x08000000f800000f

def z594 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8f9c1fff80000004 0x48f9c1fff8000000

def z595 : W := mkw 0x008d60b7c2af49f9 0xc008d60b7c2af49f 0x801fe07f803f00f2 0x0801fe07f803f00f

def z596 : W := mkw 0x7fffbf5a7ffffecf 0x07fffbf5a7ffffec 0xfffffffe7fffffcf 0xffffffffe7fffffc

def z597 : W := mkw 0x0004001040204080 0x0000400104020408 0xe19c13f04620c7cf 0x6e19c13f04620c7c

def z598 : W := mkw 0x5f52b84a3d9da84d 0x05f52b84a3d9da84 0x1e62ec0e39dc3800 0x91e62ec0e39dc380

def z599 : W := mkw 0x3f767f5efdfdfedf 0x43f767f5efdfdfed 0xffffffffffffffff 0xffffffffffffffff

def z600 : W := mkw 0x008900a102020120 0x8008900a10202012 0xe1810381862307ff 0x2e1810381862307f

def z601 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xa19c13f1c600c7f4 0x4a19c13f1c600c7f

def z602 : W := mkw 0x000000000800a004 0x0000000000800a00 0x300000007800f808 0x1300000007800f80

def z603 : W := mkw 0x4fffbf0077bb0008 0x04fffbf0077bb000 0x5fffff807fff000f 0xf5fffff807fff000

def z604 : W := mkw 0x0000000000401400 0x0000000000040140 0x6000000001c03c08 0x16000000001c03c0

def z605 : W := mkw 0x100400125834e8c5 0x0100400125834e8c 0xb01c1070783cf8ce 0x7b01c1070783cf8c

def z606 : W := mkw 0x0d56000075300000 0x00d5600007530000 0x5ffe00007ffc000b 0xf5ffe00007ffc000

def z607 : W := mkw 0x008d00a142220120 0x8008d00a14222012 0x419d0381c623073b 0x6419d0381c623073

def z608 : W := mkw 0x92205fff8804e8c5 0x092205fff8804e8c 0xa0001fff8000f8c4 0x0a0001fff8000f8c

def z609 : W := mkw 0x0000600680cd1c59 0x40000600680cd1c5 0xe003e00f81ff3cfa 0x1e003e00f81ff3cf

def z610 : W := mkw 0x2b603f022dcdbe5f 0x42b603f022dcdbe5 0x7fe01f807ffffffd 0xf7fe01f807ffffff

def z611 : W := mkw 0x29e907a127421722 0x829e907a12742172 0x41e1038187c30731 0x041e1038187c3073

def z612 : W := mkw 0x200020022dcdbe5f 0x4200020022dcdbe5 0x700000007ffffff8 0x1700000007ffffff

def z613 : W := mkw 0x220019000800a206 0x0220019000800a20 0x000011800000c300 0x0000011800000c30

def z614 : W := mkw 0x0412004800000000 0x0041200480000000 0x801e007e00000002 0x0801e007e0000000

def z615 : W := mkw 0x120018580800e084 0x0120018580800e08 0x000010700000c000 0x0000010700000c00

def z616 : W := mkw 0x8f72ff4e80cd1c59 0x48f72ff4e80cd1c5 0x0e62ec0e01dc3800 0x90e62ec0e01dc380

def z617 : W := mkw 0x89e9e7a580c91418 0x489e9e7a580c9141 0x41e1e38181c30431 0x041e1e38181c3043

def z618 : W := mkw 0xcfffff4cf7bb0008 0x0cfffff4cf7bb000 0x5fffec0e7fff000b 0xf5fffec0e7fff000

def z619 : W := mkw 0x00040010422241a0 0x800040010422241a 0x000000004600c300 0x0000000004600c30

def z620 : W := mkw 0x0020260200cd1c59 0x40020260200cd1c5 0x60600e0001ff3cfd 0xb60600e0001ff3cf

def z621 : W := mkw 0x00006006808d0859 0x400006006808d085 0x0002e00e001c0000 0x00002e00e001c000

def z622 : W := mkw 0x8ffbdf4c80000000 0x08ffbdf4c8000000 0x0fffec0e00000003 0xe0fffec0e0000000

def z623 : W := mkw 0x5616385a7fbfe8cd 0x05616385a7fbfe8c 0xfe1e1c7e7ffff8ce 0xffe1e1c7e7ffff8c

def z624 : W := mkw 0x1200184a0804a845 0x01200184a0804a84 0x00000c0e00003800 0x000000c0e0000380

def z625 : W := mkw 0x00246616c0ed5cd9 0x400246616c0ed5cd 0xe07ffe7fc1fffcff 0xfe07ffe7fc1fffcf

def z626 : W := mkw 0x408d20b177bb41a8 0x8408d20b177bb41a 0xf19d13f1ffffc7ff 0x7f19d13f1ffffc7f

def z627 : W := mkw 0xcdffe7a5f7bb0008 0x0cdffe7a5f7bb000 0x5fffe381ffff000b 0xf5fffe381ffff000

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001020180000007 0x2800102018000000

def z629 : W := mkw 0x5ffffe5efffffcdd 0x45ffffe5efffffcd 0xfffffe7ffffffcff 0xffffffe7ffffffcf

def z630 : W := mkw 0x09cd000067220000 0x009cd00006722000 0x5ffd00007fe3000b 0xf5ffd00007fe3000

def z631 : W := mkw 0x169f185a5a36e8c5 0x0169f185a5a36e8c 0xff9f1c7e7e3ff8cf 0xfff9f1c7e7e3ff8c

def z632 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x3e601f8039c0ff04 0x93e601f8039c0ff0

def z633 : W := mkw 0x9fffffffd8fdfcdd 0x49fffffffd8fdfcd 0xfffffffff9fffcff 0xffffffffff9fffcf

def z634 : W := mkw 0x4ddfa00277ff1c59 0x44ddfa00277ff1c5 0x7fffe0007fff3cfb 0xf7fffe0007fff3cf

def z635 : W := mkw 0x3f761f587d70f686 0x03f761f587d70f68 0x7ffc1ff07fc0ff0d 0xf7ffc1ff07fc0ff0

def z636 : W := mkw 0x1616184a5834a845 0x01616184a5834a84 0x1e1e0c0e783c380a 0xf1e1e0c0e783c380

def z637 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0x4063ee0f81df3c31 0x94063ee0f81df3c3

def z638 : W := mkw 0x149f00fb523649e1 0x8149f00fb523649e 0x801f007f803f00f2 0x0801f007f803f00f

def z639 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x5fe00c007fc03809 0xf5fe00c007fc0380

def z640 : W := mkw 0x1616185a5a36e9e5 0x81616185a5a36e9e 0xfe1e1c7e7e3ffffe 0xffe1e1c7e7e3ffff

def z641 : W := mkw 0x6ddfa0007ffbb60e 0x06ddfa0007ffbb60 0x7fffe0007fffff0b 0xf7fffe0007fffff0

def z642 : W := mkw 0x0612184800000000 0x0061218480000000 0x0e1c107000000000 0x40e1c10700000000

def z643 : W := mkw 0x2be91fa12d40b606 0x02be91fa12d40b60 0xfffd1ff1ffc0ff0f 0xffffd1ff1ffc0ff0

def z644 : W := mkw 0x9fffdffdd830e084 0x09fffdffdd830e08 0x9ffffffff800c007 0xe9ffffffff800c00

def z645 : W := mkw 0x3f56195a7d34eac7 0x03f56195a7d34eac 0xbf9e1dfe7e3cfbce 0xfbf9e1dfe7e3cfbc

def z646 : W := mkw 0x202006002d40b606 0x0202006002d40b60 0x70600e007fc0ff0d 0xb70600e007fc0ff0

def z647 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x0e600c0000000000 0x80e600c000000000

def z648 : W := mkw 0x2b4019002d00a206 0x02b4019002d00a20 0x5fe011807fc0c309 0xf5fe011807fc0c30

def z649 : W := mkw 0x8fffdfedc2220000 0x08fffdfedc222000 0xcfffffffc623000f 0xecfffffffc623000

def z650 : W := mkw 0x000000a100000000 0x0000000a10000000 0x800013f180000004 0x0800013f18000000

def z651 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xc19d03f1862307f3 0x0c19d03f1862307f

def z652 : W := mkw 0x0416000050300000 0x0041600005030000 0x001e0000003c0002 0x0001e0000003c000

def z653 : W := mkw 0x4dffe604f7bb0008 0x04dffe604f7bb000 0xdfffee0fffff000f 0xfdfffee0fffff000

def z654 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xa062ec0e01fc38ce 0xba062ec0e01fc38c

def z655 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xa01d13f18023c7f6 0x0a01d13f18023c7f

def z656 : W := mkw 0x100400105830e084 0x0100400105830e08 0x100000007800c000 0x0100000007800c00

def z657 : W := mkw 0x0020060000401400 0x0002006000040140 0xe0610e0181e33cff 0xbe0610e0181e33cf

def z658 : W := mkw 0x2f761f007d70b606 0x02f761f007d70b60 0x7ffe1f807ffcff0f 0xf7ffe1f807ffcff0

def z659 : W := mkw 0x002046b780445df1 0xc002046b780445df 0xa0001fff8000fff4 0x0a0001fff8000fff

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0x00020000003c000a 0xb00020000003c000

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0x4060000001c00009 0xb4060000001c0000

def z662 : W := mkw 0x300400127d74fec7 0x0300400127d74fec 0x700000007ffcffc8 0x1700000007ffcffc

def z663 : W := mkw 0x00006006808d0859 0x400006006808d085 0xc063e00f81ff00fb 0xbc063e00f81ff00f

def z664 : W := mkw 0x1412004a10140841 0x01412004a1014084 0x0002000e001c0000 0x00002000e001c000

def z665 : W := mkw 0x00002002008d0859 0x400002002008d085 0x00000000003f00f0 0x000000000003f00f

def z666 : W := mkw 0x0020060000000000 0x0002006000000000 0x00600e0000000005 0xa00600e000000000

def z667 : W := mkw 0x00206606808d0859 0x400206606808d085 0x8063ee0f803f00f7 0xa8063ee0f803f00f

def z668 : W := mkw 0x2b601f000840b606 0x02b601f000840b60 0x2fe01f800000ff05 0xe2fe01f800000ff0

def z669 : W := mkw 0x0000000000000000 0x0000000000000000 0x80020c0e00000006 0xa80020c0e0000000

def z670 : W := mkw 0x3f721f4a3d54be47 0x03f721f4a3d54be4 0x7fe21f8e7fdcff0d 0xf7fe21f8e7fdcff0

def z671 : W := mkw 0x0020660480890008 0x0002066048089000 0xc063ee0f81ff000f 0xbc063ee0f81ff000

def z672 : W := mkw 0x069f18f9422241a0 0x8069f18f9422241a 0xef9f1fffc623c7ff 0xeef9f1fffc623c7f

def z673 : W := mkw 0x008d000042220000 0x0008d00004222000 0x619d13804623c70f 0x6619d13804623c70

def z674 : W := mkw 0x0616184850300000 0x0061618485030000 0x9e1e1c7e783c000e 0xf9e1e1c7e783c000

def z675 : W := mkw 0x008d00b140204080 0x0008d00b14020408 0xa19d13f1c020c0cf 0x6a19d13f1c020c0c

def z676 : W := mkw 0x4ddfa00052bb0008 0x04ddfa00052bb000 0x0fffe000003f0003 0xe0fffe000003f000

def z677 : W := mkw 0x0416000050300000 0x0041600005030000 0x1e1c000078000000 0x41e1c00007800000

def z678 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x0fe3ef8f80000001 0x80fe3ef8f8000000

def z679 : W := mkw 0x100400125a36e9e5 0x8100400125a36e9e 0x700000007e3ffff8 0x1700000007e3ffff

def z680 : W := mkw 0xcffbffeda78b0008 0x0cffbffeda78b000 0xcfffffff87c30007 0xecfffffff87c3000

def z681 : W := mkw 0x0ddf800050300000 0x00ddf80005030000 0x1fffe000783c000b 0xf1fffe000783c000

def z682 : W := mkw 0x169f18f95a32e1a4 0x8169f18f95a32e1a 0x1f9c11f07e00c300 0x41f9c11f07e00c30

def z683 : W := mkw 0x4004200052bb0008 0x04004200052bb000 0x00000000003f0000 0x000000000003f000

def z684 : W := mkw 0x4d72e606b5dd1c59 0x44d72e606b5dd1c5 0xfe63ee0fb9ff3cff 0xbfe63ee0fb9ff3cf

def z685 : W := mkw 0x061618005830a004 0x0061618005830a00 0x3e1e1c00783cf80e 0xf3e1e1c00783cf80

def z686 : W := mkw 0x849fc0fdc22241a0 0x8849fc0fdc22241a 0x801fe07f802300f2 0x0801fe07f802300f

def z687 : W := mkw 0x0200184800000000 0x0020018480000000 0x80001c7e00000004 0x080001c7e0000000

def z688 : W := mkw 0x0b605f0480000000 0x00b605f048000000 0x8fe3ff8f80000007 0xe8fe3ff8f8000000

def z689 : W := mkw 0x408d200077bb0008 0x0408d200077bb000 0x519d00007fff000b 0x7519d00007fff000

def z690 : W := mkw 0x8be9dfa580000000 0x08be9dfa58000000 0x0fe1ff8180000005 0xe0fe1ff818000000

def z691 : W := mkw 0x000400b1402041a0 0x8000400b1402041a 0xa01c13f1c020c7fe 0x6a01c13f1c020c7f

def z692 : W := mkw 0x22201f002d40b606 0x022201f002d40b60 0x70001f807fc0ff0c 0x170001f807fc0ff0

def z693 : W := mkw 0x00040010422241a0 0x800040010422241a 0xe0010201c623c7ff 0x2e0010201c623c7f

def z694 : W := mkw 0x1436665ed0fd5cd9 0x41436665ed0fd5cd 0xe07fee7f81ff3cff 0xbe07fee7f81ff3cf

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x600002000000040d 0x2600002000000040

def z696 : W := mkw 0x2960070025401602 0x0296007002540160 0x61e00f8007c03f0d 0xb61e00f8007c03f0

def z697 : W := mkw 0x1612184a1814a845 0x01612184a1814a84 0x3e021c0e781cf80c 0xf3e021c0e781cf80

def z698 : W := mkw 0x00006006808d0859 0x400006006808d085 0xe003e20f803f04ff 0x2e003e20f803f04f

def z699 : W := mkw 0x29ed07b1676257a2 0x829ed07b1676257a 0xe1fd13f1c7e3c7ff 0x6e1fd13f1c7e3c7f

def z700 : W := mkw 0x3616185a7d74fec7 0x03616185a7d74fec 0xfe1e1c7e7ffcffce 0xffe1e1c7e7ffcffc

def z701 : W := mkw 0x020018020804a845 0x0020018020804a84 0xbe021c0e783cf8ce 0xfbe021c0e783cf8c

def z702 : W := mkw 0x0000000000000000 0x0000000000000000 0x400100000023000b 0x2400100000023000

def z703 : W := mkw 0x600420007ffbb60e 0x0600420007ffbb60 0x700000007fffff08 0x1700000007fffff0

def z704 : W := mkw 0x0940000025000000 0x0094000002500000 0x1f8000007e000000 0x41f8000007e00000

def z705 : W := mkw 0x820019e900000000 0x0820019e90000000 0x000011f000000000 0x0000011f00000000

def z706 : W := mkw 0x569fb85a5abfe8cd 0x0569fb85a5abfe8c 0xbe1ffc7e783ff8ce 0xfbe1ffc7e783ff8c

def z707 : W := mkw 0x8ffbdfed80401400 0x08ffbdfed8040140 0xefffffffc7c0ff0f 0xfefffffffc7c0ff0

def z708 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0xffffe271ffff04ff 0xfffffe271ffff04f

def z709 : W := mkw 0x4ddfa0a177bb0008 0x04ddfa0a177bb000 0x5fffe381ffff000b 0xf5fffe381ffff000

def z710 : W := mkw 0x8ffbdfed90100000 0x08ffbdfed9010000 0x9fffffffb81c0007 0xf9fffffffb81c000

def z711 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x3e1e1c7e783cf8c8 0xd3e1e1c7e783cf8c

def z712 : W := mkw 0x869bd8ed80000000 0x0869bd8ed8000000 0x8e1ff07f80000002 0x48e1ff07f8000000

def z713 : W := mkw 0x0612184800000000 0x0061218480000000 0x8e7ffc7e00000007 0xe8e7ffc7e0000000

def z714 : W := mkw 0x4d52a0b1359941a8 0x84d52a0b1359941a 0xbe62f3f1b9dcc7f4 0x9be62f3f1b9dcc7f

def z715 : W := mkw 0x020418124824e8c5 0x0020418124824e8c 0xbe1e1c7e783cf8ce 0xfbe1e1c7e783cf8c

def z716 : W := mkw 0x4ddba000379b0008 0x04ddba000379b000 0x5fe3e0007fdf0009 0xf5fe3e0007fdf000

def z717 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1e1ffe783cffce 0xfbe1e1ffe783cffc

def z718 : W := mkw 0x1616185a5834e9e5 0x81616185a5834e9e 0xbe1e1c7e783cfffe 0xfbe1e1c7e783cfff

def z719 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0xdfffe201ffff000f 0xfdfffe201ffff000

def z720 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xe19f13f1c63fc7ff 0xfe19f13f1c63fc7f

def z721 : W := mkw 0x4dffc606f7761c51 0x44dffc606f7761c5 0xbf9c0e0ffe003cf4 0x4bf9c0e0ffe003cf

def z722 : W := mkw 0x6ddfa10077bb020a 0x06ddfa10077bb020 0x5fffe1807fff030b 0xf5fffe1807fff030

def z723 : W := mkw 0x5ddfa05877bb4088 0x05ddfa05877bb408 0x5fffe0707fff000b 0xf5fffe0707fff000

def z724 : W := mkw 0x22ad5fb7ca66fff7 0xc22ad5fb7ca66fff 0xe19d1fffc623ffff 0x6e19d1fffc623fff

def z725 : W := mkw 0x8f76df5cc22241a0 0x88f76df5cc22241a 0x6e62ec0e4623c7f8 0x86e62ec0e4623c7f

def z726 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x819ff1ff80000002 0x4819ff1ff8000000

def z727 : W := mkw 0xaffbdfed8840b606 0x0affbdfed8840b60 0xbffffffff800ff0f 0xfbffffffff800ff0

def z728 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x0fffffff80000001 0xc0fffffff8000000

def z729 : W := mkw 0x16367e5cd8f9f49c 0x416367e5cd8f9f49 0x5e7df271f9c3c431 0x45e7df271f9c3c43

def z730 : W := mkw 0x300420127dfdfedf 0x4300420127dfdfed 0x700000007ffffff8 0x1700000007ffffff

def z731 : W := mkw 0x500420127ffffcdd 0x4500420127ffffcd 0x700000007ffffcf8 0x1700000007ffffcf

def z732 : W := mkw 0x8fdbb9eb00cd1c59 0x48fdbb9eb00cd1c5 0x6f9c11f001ff3cf8 0x56f9c11f001ff3cf

def z733 : W := mkw 0x86bbdfed80000000 0x086bbdfed8000000 0x8e1fffff80000006 0xe8e1fffff8000000

def z734 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x819fe3ff80000003 0x0819fe3ff8000000

def z735 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0xffffe071ffffc7fb 0xfffffe071ffffc7f

def z736 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0x1ffefdfe7fc0fb00 0xd1ffefdfe7fc0fb0

def z737 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x1e63e00039ff0002 0x91e63e00039ff000

def z738 : W := mkw 0x4ddfa01077bb4088 0x04ddfa01077bb408 0xfffff3f07fffc7cf 0xffffff3f07fffc7c

def z739 : W := mkw 0x5004201277bf48c9 0x05004201277bf48c 0x500000007fff00c8 0x1500000007fff00c

def z740 : W := mkw 0x4d56a00075b90008 0x04d56a00075b9000 0x1e7ee00079dc0000 0xd1e7ee00079dc000

def z741 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0x9e7fec7fb9c03802 0x99e7fec7fb9c0380

def z742 : W := mkw 0x8ffbdfed82020000 0x08ffbdfed8202000 0xcfffffff86030007 0xecfffffff8603000

def z743 : W := mkw 0x8ffbdfed80000120 0x88ffbdfed8000012 0x8fffffff80000737 0xe8fffffff8000073

def z744 : W := mkw 0x4004201277ff5df9 0xc4004201277ff5df 0x700000007ffffff8 0x1700000007ffffff

def z745 : W := mkw 0x200420126fefffff 0xc200420126feffff 0x700000007ffffff8 0x1700000007ffffff

def z746 : W := mkw 0x8ffbdfeda5000000 0x08ffbdfeda500000 0xcfffffff87c00007 0xecfffffff87c0000

def z747 : W := mkw 0x66bfbf005afbb60e 0x066bfbf005afbb60 0x201fff80003fff06 0x0201fff80003fff0

def z748 : W := mkw 0xcddfa0e977bb0008 0x0cddfa0e977bb000 0x5fffe0707fff000b 0xf5fffe0707fff000

def z749 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x801fe27f80000007 0x2801fe27f8000000

def z750 : W := mkw 0x0940200025890008 0x0094020002589000 0x1e62e00039dc0000 0x91e62e00039dc000

def z751 : W := mkw 0x2b605f04ad40b606 0x02b605f04ad40b60 0xffe01f8fffc0ff0d 0xfffe01f8fffc0ff0

def z752 : W := mkw 0x8ddbc0ed80000000 0x08ddbc0ed8000000 0x8ffff3ff80000007 0xe8ffff3ff8000000

def z753 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1e1e7ff83cfcfe 0xfbe1e1e7ff83cfcf

def z754 : W := mkw 0x12205e5e8844fcd5 0x412205e5e8844fcd 0xa0001c7e0000f8c4 0x0a0001c7e0000f8c

def z755 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0xfffff1f07fffc3cf 0xffffff1f07fffc3c

def z756 : W := mkw 0x869bd8ed80000000 0x0869bd8ed8000000 0x801ffc7f80000006 0x0801ffc7f8000000

def z757 : W := mkw 0x4d52a000379b0008 0x04d52a000379b000 0x5e62e0003fdf0000 0x95e62e0003fdf000

def z758 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8ffeffff80000004 0xc8ffeffff8000000

def z759 : W := mkw 0xaf72df4cad40b606 0x0af72df4cad40b60 0xbe7efc7e79c0f80e 0xfbe7efc7e79c0f80

def z760 : W := mkw 0xa6bbdfed8840b606 0x0a6bbdfed8840b60 0xa01fffff8000ff06 0x0a01fffff8000ff0

def z761 : W := mkw 0xaffbdfedad00a206 0x0affbdfedad00a20 0x9fffffffb8000007 0xe9fffffffb800000

def z762 : W := mkw 0x0960060025401400 0x0096006002540140 0x7fe01f807fc0ff0d 0xf7fe01f807fc0ff0

def z763 : W := mkw 0x1616184a5834a845 0x01616184a5834a84 0x9e1e1c7e783c380e 0xf9e1e1c7e783c380

def z764 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xcfffffff81c0000f 0xfcfffffff81c0000

def z765 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xe1fff3f1c623c7ff 0xee1fff3f1c623c7f

def z766 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xafffffffc000c00f 0xeafffffffc000c00

def z767 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xcfffffffc600000f 0xecfffffffc600000

def z768 : W := mkw 0x8ffbdfed82020120 0x88ffbdfed8202012 0xefffffffc603c73f 0xeefffffffc603c73

def z769 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0xdfffe001ffff00fb 0xfdfffe001ffff00f

def z770 : W := mkw 0x008940a580000000 0x0008940a58000000 0x819ff3ff80000007 0x6819ff3ff8000000

def z771 : W := mkw 0x8fdbd9ed80000000 0x08fdbd9ed8000000 0x0f9ef1fe00000000 0x40f9ef1fe0000000

def z772 : W := mkw 0x3d76075a75745ec3 0x03d76075a75745ec 0xc1fe03fe07fc07c3 0x0c1fe03fe07fc07c

def z773 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x1fe2e00039dc0001 0xf1fe2e00039dc000

def z774 : W := mkw 0x4ddfa04877bb0008 0x04ddfa04877bb000 0xdfffe07e7fff000b 0xfdfffe07e7fff000

def z775 : W := mkw 0x22205f068844be57 0x422205f068844be5 0xe1811f8fc623ffff 0x6e1811f8fc623fff

def z776 : W := mkw 0x22205f068844be57 0x422205f068844be5 0x20001f8e0000ff04 0x020001f8e0000ff0

def z777 : W := mkw 0xaffbdfedad00a206 0x0affbdfedad00a20 0xbffffffffe00fb0f 0xfbffffffffe00fb0

def z778 : W := mkw 0x84bbc6ed80000000 0x084bbc6ed8000000 0x807fe27f80000003 0x0807fe27f8000000

def z779 : W := mkw 0x99edc7b7d834e8c5 0x099edc7b7d834e8c 0x31e1e381f83cf8c9 0x131e1e381f83cf8c

def z780 : W := mkw 0x4944200077bb0008 0x04944200077bb000 0x5fe3e0007fff000b 0xf5fe3e0007fff000

def z781 : W := mkw 0xc2247fedf7bb0008 0x0c2247fedf7bb000 0xd0001fffffff000c 0x1d0001fffffff000

def z782 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7fe01d807fc0ff08 0xd7fe01d807fc0ff0

def z783 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0xdffff0707fff000f 0xfdffff0707fff000

def z784 : W := mkw 0x5fdf98f97f32e1a4 0x85fdf98f97f32e1a 0x1f9c11f07e00c300 0x41f9c11f07e00c30

def z785 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x1e1e0c7e381c3800 0x91e1e0c7e381c380

def z786 : W := mkw 0x049f20b152bb41a8 0x8049f20b152bb41a 0xfffff3f1ffffc7ff 0xffffff3f1ffffc7f

def z787 : W := mkw 0x869bd8ed80000000 0x0869bd8ed8000000 0x8f9fffff80000007 0xe8f9fffff8000000

def z788 : W := mkw 0x4d56a00075b90008 0x04d56a00075b9000 0x1e62e00079fc0008 0x91e62e00079fc000

def z789 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0xfe63e201b9ff04ff 0xbfe63e201b9ff04f

def z790 : W := mkw 0x169b18eb1a16a965 0x8169b18eb1a16a96 0x5f830f8fbe1f3f31 0x95f830f8fbe1f3f3

def z791 : W := mkw 0xaffbdfed8840b606 0x0affbdfed8840b60 0xefffffffc600ff0f 0xeefffffffc600ff0

def z792 : W := mkw 0x0940200025890008 0x0094020002589000 0xffe3f381ffffc7ff 0xfffe3f381ffffc7f

def z793 : W := mkw 0x4ddfa00077bb0128 0x84ddfa00077bb012 0x5fffe0007fff073b 0xf5fffe0007fff073

def z794 : W := mkw 0x8ddbc0ed80000000 0x08ddbc0ed8000000 0x8f9fe07f80000002 0x48f9fe07f8000000

def z795 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xe19d13f18623c7f7 0x0e19d13f18623c7f

def z796 : W := mkw 0xaffbdfeda5401602 0x0affbdfeda540160 0x8fffffff81c00007 0xe8fffffff81c0000

def z797 : W := mkw 0xaffbdfeda7421722 0x8affbdfeda742172 0xcfffffff87c30737 0xecfffffff87c3073

def z798 : W := mkw 0x4ddba00035990008 0x04ddba0003599000 0x1e7fe00039dc0002 0x91e7fe00039dc000

def z799 : W := mkw 0x149f60ffd2bf49f9 0xc149f60ffd2bf49f 0x801fe07f803f00f2 0x0801fe07f803f00f

def z800 : W := mkw 0x1004201258bde8cd 0x01004201258bde8c 0x7000000079fff8c8 0x17000000079fff8c

def z801 : W := mkw 0x500420127fbfe9ed 0x8500420127fbfe9e 0x700000007ffffff8 0x1700000007ffffff

def z802 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5fffe0007fdf0001 0xd5fffe0007fdf000

def z803 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x3fe01f807fc0ff04 0xd3fe01f807fc0ff0

def z804 : W := mkw 0x4ddba00035990008 0x04ddba0003599000 0x5fffe00039ff000b 0xf5fffe00039ff000

def z805 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x5e63e00039df0001 0x95e63e00039df000

def z806 : W := mkw 0x869bd8ed8800a004 0x0869bd8ed8800a00 0xbe1ffc7ff800f80e 0xfbe1ffc7ff800f80

def z807 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x9e1e1c7e781cf806 0xf9e1e1c7e781cf80

def z808 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x7fffe0007fff04fb 0xf7fffe0007fff04f

def z809 : W := mkw 0x0b4018002d00a004 0x00b4018002d00a00 0x7fe01f807fc0ff0d 0xf7fe01f807fc0ff0

def z810 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x9e1e0c7e783c38ca 0xf9e1e0c7e783c38c

def z811 : W := mkw 0x2bed1fb16f62f7a6 0x82bed1fb16f62f7a 0x9e7d0c71b9e338f2 0x99e7d0c71b9e338f

def z812 : W := mkw 0x04160012503448c1 0x004160012503448c 0xbe1e1c7e783cf8ce 0xfbe1e1c7e783cf8c

def z813 : W := mkw 0xafdbd9edad00a206 0x0afdbd9edad00a20 0x9f9ff1fffe00c302 0x49f9ff1fffe00c30

def z814 : W := mkw 0x4ddba000379b0008 0x04ddba000379b000 0x1e63e00039df0000 0x91e63e00039df000

def z815 : W := mkw 0x8f72df4c80000000 0x08f72df4c8000000 0x8e7eec7e00000002 0x88e7eec7e0000000

def z816 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0xdffff3f1ffffc30f 0xfdffff3f1ffffc30

def z817 : W := mkw 0x1616185a5a36e8c5 0x01616185a5a36e8c 0xfe1e1c7e7e3ff8ce 0xffe1e1c7e7e3ff8c

def z818 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xcfffffff8023000f 0xecfffffff8023000

def z819 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x0ffffdfe00000003 0xe0ffffdfe0000000

def z820 : W := mkw 0xa49bc0edad40b606 0x0a49bc0edad40b60 0xf01fe07fffc0ff0a 0x1f01fe07fffc0ff0

def z821 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x1e1e1c7e783cf80a 0xf1e1e1c7e783cf80

def z822 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xff9f1ffffe3fffff 0xfff9f1ffffe3ffff

def z823 : W := mkw 0x500420125abfe8cd 0x0500420125abfe8c 0x30000000783ff8c8 0x130000000783ff8c

def z824 : W := mkw 0x008920a300cd1c59 0x4008920a300cd1c5 0xe19d13f181ff3cff 0x7e19d13f181ff3cf

def z825 : W := mkw 0x8ddbc0ed80000000 0x08ddbc0ed8000000 0x8e7fe07f80000002 0x88e7fe07f8000000

def z826 : W := mkw 0x0940200025890008 0x0094020002589000 0x5fe2e0007fdc0009 0xf5fe2e0007fdc000

def z827 : W := mkw 0xc9e9e7a5a7cb1418 0x4c9e9e7a5a7cb141 0x41e1e38187c30431 0x041e1e38187c3043

def z828 : W := mkw 0x00244614c22241a0 0x800244614c22241a 0xe063ee0fc623c7ff 0xae063ee0fc623c7f

def z829 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xcfffffff86000707 0xecfffffff8600070

def z830 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xafffffff8000c707 0xeafffffff8000c70

def z831 : W := mkw 0xadfbc7eda5401602 0x0adfbc7eda540160 0xc1ffe3ff87c00703 0x0c1ffe3ff87c0070

def z832 : W := mkw 0x4ddfa0b177bb4088 0x04ddfa0b177bb408 0xfffff3f1ffffc0cf 0xffffff3f1ffffc0c

def z833 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xe19d1ff1c623ffff 0xfe19d1ff1c623fff

def z834 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8e7fffff80000006 0x88e7fffff8000000

def z835 : W := mkw 0x8ffbdfed8800a004 0x08ffbdfed8800a00 0xafffffff8000f807 0xeafffffff8000f80

def z836 : W := mkw 0x4d56a01077bb41a8 0x84d56a01077bb41a 0x7e62e0007fffc7f8 0x97e62e0007fffc7f

def z837 : W := mkw 0x4416200077bb0008 0x04416200077bb000 0x5e7fe0007fff000b 0xf5e7fe0007fff000

def z838 : W := mkw 0x1612184a1814a845 0x01612184a1814a84 0x1e1e1c7e381c3800 0xd1e1e1c7e381c380

def z839 : W := mkw 0x2b643f126fefffff 0xc2b643f126feffff 0x7fe01f807ffffffd 0xf7fe01f807ffffff

def z840 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0x7fffe381ffffc7fb 0xf7fffe381ffffc7f

def z841 : W := mkw 0x0416201050b94088 0x00416201050b9408 0xfe7ff271f9ffc4ff 0xffe7ff271f9ffc4f

def z842 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5fe3e0007fff0009 0x95fe3e0007fff000

def z843 : W := mkw 0x00002002008d0849 0x000002002008d084 0xe063ee0f81ff3cff 0xbe063ee0f81ff3cf

def z844 : W := mkw 0xaf72df4cad40b606 0x0af72df4cad40b60 0xfffefffe7fc0ff0f 0xffffefffe7fc0ff0

def z845 : W := mkw 0x8f72df4c80000000 0x08f72df4c8000000 0x0e7efc7e00000000 0xc0e7efc7e0000000

def z846 : W := mkw 0x1612185a1814e8c5 0x01612185a1814e8c 0xbe1e1c7e381cf8c6 0xfbe1e1c7e381cf8c

def z847 : W := mkw 0x00a946a580401400 0x000a946a58040140 0xe1ffffffc7c0ff0f 0xfe1ffffffc7c0ff0

def z848 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0x7ffff3f07fffc70f 0xf7ffff3f07fffc70

def z849 : W := mkw 0x8412c04c80000000 0x08412c04c8000000 0x801ee07e00000002 0x0801ee07e0000000

def z850 : W := mkw 0x4d56a00077bb0008 0x04d56a00077bb000 0x5e63e0007fff000b 0xb5e63e0007fff000

def z851 : W := mkw 0x0004201242ef5df9 0xc0004201242ef5df 0x6000000001ff3cf8 0x16000000001ff3cf

def z852 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0xffffffffffe3ffff 0xfffffffffffe3fff

def z853 : W := mkw 0x8f72df4c80000000 0x08f72df4c8000000 0x8ffefffe00000007 0xe8ffefffe0000000

def z854 : W := mkw 0x49cda00077bb0008 0x049cda00077bb000 0x5fe1e0007fff0009 0xf5fe1e0007fff000

def z855 : W := mkw 0x0412404c80000000 0x00412404c8000000 0x801fe07f80000002 0x0801fe07f8000000

def z856 : W := mkw 0x1004201250fd5cd9 0x41004201250fd5cd 0x6000000001ff3cf8 0x16000000001ff3cf

def z857 : W := mkw 0x84bbc6ed80000000 0x084bbc6ed8000000 0x801fee7f80000006 0x0801fee7f8000000

def z858 : W := mkw 0x449fe0b7d2bf49f9 0xc449fe0b7d2bf49f 0x801fe07f803f00f2 0x0801fe07f803f00f

def z859 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8fffffff802300f7 0xe8fffffff802300f

def z860 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5fffe201ffff043b 0xf5fffe201ffff043

def z861 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1e1c7e781cf8c4 0xdbe1e1c7e781cf8c

def z862 : W := mkw 0x00ad66b7c2ef5df9 0xc00ad66b7c2ef5df 0x01fefdfe47dcfb00 0xd01fefdfe47dcfb0

def z863 : W := mkw 0x2b605f04ad40b606 0x02b605f04ad40b60 0x7fe2ff8e7fc0ff0d 0xf7fe2ff8e7fc0ff0

def z864 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0xdffff1f1ffffc3fb 0xfdffff1f1ffffc3f

def z865 : W := mkw 0x8fdbd9ed80000000 0x08fdbd9ed8000000 0x8f9ffdff80000006 0xe8f9ffdff8000000

def z866 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0xbffffffffe00ff07 0xebffffffffe00ff0

def z867 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x801ff3ff80000006 0x0801ff3ff8000000

def z868 : W := mkw 0x0004201242af49f9 0xc0004201242af49f 0x60000000463fc7f8 0x060000000463fc7f

def z869 : W := mkw 0x92205fff8844fcd5 0x492205fff8844fcd 0xa0001fff8000fcf4 0x0a0001fff8000fcf

def z870 : W := mkw 0xaffbdfedad00a206 0x0affbdfedad00a20 0xfffffffffe00c70f 0xefffffffffe00c70

def z871 : W := mkw 0x0020460480000000 0x0002046048000000 0x807ffe7f80000007 0xe807ffe7f8000000

def z872 : W := mkw 0x4ddfa0a177bb0128 0x84ddfa0a177bb012 0x5fffe001ffff003b 0xf5fffe001ffff003

def z873 : W := mkw 0xaffbdfed8800a206 0x0affbdfed8800a20 0x8fffffff8000c307 0xe8fffffff8000c30

def z874 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5ffff3807fff000f 0xf5ffff3807fff000

def z875 : W := mkw 0x0940200025890008 0x0094020002589000 0x5e63e00039ff000b 0xb5e63e00039ff000

def z876 : W := mkw 0x8dfbc7ed80000000 0x08dfbc7ed8000000 0x8fffe3ff80000003 0xe8fffe3ff8000000

def z877 : W := mkw 0x0612184a0804a845 0x00612184a0804a84 0xbe1e1c7e783cf8ce 0xfbe1e1c7e783cf8c

def z878 : W := mkw 0x0fdb98e900000000 0x00fdb98e90000000 0x8fffffff80000007 0xe8fffffff8000000

def z879 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8fffffff803c000f 0xf8fffffff803c000

def z880 : W := mkw 0xaf72ff4eadcdbe5f 0x4af72ff4eadcdbe5 0x1e62ec0e39dc3800 0x91e62ec0e39dc380

def z881 : W := mkw 0xa2205fef8844be57 0x4a2205fef8844be5 0xa0001fff8000fff4 0x0a0001fff8000fff

def z882 : W := mkw 0x06bb5eed80000000 0x006bb5eed8000000 0x8fffffff80000007 0xe8fffffff8000000

def z883 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xafffffff8000380f 0xfafffffff8000380

def z884 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0xe19ff3ffc600c70f 0x6e19ff3ffc600c70

def z885 : W := mkw 0x0ffb9f4800000000 0x00ffb9f480000000 0x8ffffffe00000007 0xe8ffffffe0000000

def z886 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x1e7ee00039dc0002 0xf1e7ee00039dc000

def z887 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0x7ffff1f07fffc7fb 0xf7ffff1f07fffc7f

def z888 : W := mkw 0x0004201240ed5cd9 0x40004201240ed5cd 0x6000000041fffcf8 0x16000000041fffcf

def z889 : W := mkw 0x1616185a5a36e9e5 0x81616185a5a36e9e 0xbe1e1c7e783ff8fe 0xfbe1e1c7e783ff8f

def z890 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0x9fffffffffc0fb07 0xf9fffffffffc0fb0

def z891 : W := mkw 0x100420125afffdfd 0xc100420125afffdf 0x700000007ffffff8 0x1700000007ffffff

def z892 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5ffff1807fffc30b 0xf5ffff1807fffc30

def z893 : W := mkw 0x869bd8ed80000000 0x0869bd8ed8000000 0x8e1fec7f80000002 0x88e1fec7f8000000

def z894 : W := mkw 0x86bbdfed80000000 0x086bbdfed8000000 0x819fffff80000007 0x6819fffff8000000

def z895 : W := mkw 0x5bc9b85a2f8fe8cd 0x05bc9b85a2f8fe8c 0xe1e1fc7e07c3f8c5 0x0e1e1fc7e07c3f8c

def z896 : W := mkw 0x4ddfa01077bb41a8 0x84ddfa01077bb41a 0xfffff0707fffc7ff 0xffffff0707fffc7f

def z897 : W := mkw 0x4ddba0a1379b0128 0x84ddba0a1379b012 0x5fe3e381bfdf0731 0x95fe3e381bfdf073

def z898 : W := mkw 0xaffbdfeda5401602 0x0affbdfeda540160 0xefffffffc7c0c70f 0xeefffffffc7c0c70

def z899 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8e7ffc7f80000006 0xe8e7ffc7f8000000

def z900 : W := mkw 0x8ddbc0ed80000000 0x08ddbc0ed8000000 0x81ffe07f80000003 0x081ffe07f8000000

def z901 : W := mkw 0x1612184a1814a845 0x01612184a1814a84 0xbe1e1c7e781cf80e 0xfbe1e1c7e781cf80

def z902 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8e7fee7f80000007 0xa8e7fee7f8000000

def z903 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x7fe2f3807fdcc70d 0xf7fe2f3807fdcc70

def z904 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xff9e1c7e7e3cf8cf 0xfff9e1c7e7e3cf8c

def z905 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xafffffff802000cf 0xeafffffff802000c

def z906 : W := mkw 0xaffbdfeda5000202 0x0affbdfeda500020 0x8fffffff86000307 0xe8fffffff8600030

def z907 : W := mkw 0x8ffbdfed82020120 0x88ffbdfed8202012 0xefffffff862307ff 0xeefffffff862307f

def z908 : W := mkw 0x2f725f4cad40b606 0x02f725f4cad40b60 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z909 : W := mkw 0x8dfbc7ed80000000 0x08dfbc7ed8000000 0x81ffefff80000007 0xa81ffefff8000000

def z910 : W := mkw 0x4d56a00075b90008 0x04d56a00075b9000 0x5ffee0007ffc000b 0xf5ffee0007ffc000

def z911 : W := mkw 0x84bbc6ed80401400 0x084bbc6ed8040140 0xe07fee7f81c03c0f 0xbe07fee7f81c03c0

def z912 : W := mkw 0x0f52984800000000 0x00f5298480000000 0x8e7efc7e00000006 0xe8e7efc7e0000000

def z913 : W := mkw 0x8be9dfed80000000 0x08be9dfed8000000 0x81fdffff80000007 0x681fdffff8000000

def z914 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x1ffee0007ffc000a 0xf1ffee0007ffc000

def z915 : W := mkw 0x1416005a503448c1 0x01416005a503448c 0xbe1e0c7e783c38ce 0xfbe1e0c7e783c38c

def z916 : W := mkw 0x4d56a00077bb0008 0x04d56a00077bb000 0x1e62e0007fdc0000 0x91e62e0007fdc000

def z917 : W := mkw 0x294000002d40b606 0x0294000002d40b60 0x7fe013807fc0ff0d 0xf7fe013807fc0ff0

def z918 : W := mkw 0x4ddfa01077bb4088 0x04ddfa01077bb408 0x5ffff0707fffc00b 0xf5ffff0707fffc00

def z919 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe063ee0fc7ffffff 0xbe063ee0fc7fffff

def z920 : W := mkw 0x4d56a00077bb0008 0x04d56a00077bb000 0x5fe2e0007fff0009 0xf5fe2e0007fff000

def z921 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xc19d13f1c623c7f3 0x4c19d13f1c623c7f

def z922 : W := mkw 0x8ffbdfeda5000000 0x08ffbdfeda500000 0x9fffffffb9c00007 0xf9fffffffb9c0000

def z923 : W := mkw 0x1616185a5a36e9e5 0x81616185a5a36e9e 0xfe1f1e7ffe3fffff 0xffe1f1e7ffe3ffff

def z924 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0xfffff381ffffc7ff 0xffffff381ffffc7f

def z925 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x801ff07f80000006 0x6801ff07f8000000

def z926 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7fe11f807fe3ff0f 0xf7fe11f807fe3ff0

def z927 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0x619d13f1c623c7f9 0x4619d13f1c623c7f

def z928 : W := mkw 0xcffbdfedb5100000 0x0cffbdfedb510000 0x9fffffffb8000007 0xe9fffffffb800000

def z929 : W := mkw 0x2b605f04ad40b606 0x02b605f04ad40b60 0xffe3ff8fffe3ffff 0xfffe3ff8fffe3fff

def z930 : W := mkw 0x86325fed80000000 0x086325fed8000000 0x8e7fffff80000007 0xe8e7fffff8000000

def z931 : W := mkw 0x4ddba000379b0008 0x04ddba000379b000 0x5fffe0003fdf0003 0xf5fffe0003fdf000

def z932 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0x5ffff3f1ffffc73b 0xf5ffff3f1ffffc73

def z933 : W := mkw 0x3b643f127dfdfedf 0x43b643f127dfdfed 0x7fe01f807ffffffd 0xf7fe01f807ffffff

def z934 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0x9e7fe071b9ff00f2 0x99e7fe071b9ff00f

def z935 : W := mkw 0x700420127ffffecf 0x0700420127ffffec 0x700000007fffffc8 0x1700000007fffffc

def z936 : W := mkw 0x061618485830a004 0x0061618485830a00 0xbe1e1c7e783cf80e 0xfbe1e1c7e783cf80

def z937 : W := mkw 0x22205fb78844fff7 0xc22205fb78844fff 0xa0001fff8000fff4 0x0a0001fff8000fff

def z938 : W := mkw 0x84bbc6ed80000000 0x084bbc6ed8000000 0x807fec7f80000002 0x8807fec7f8000000

def z939 : W := mkw 0x4d56a01075b94088 0x04d56a01075b9408 0xbe7ef07079fcc0ce 0xfbe7ef07079fcc0c

def z940 : W := mkw 0x8fdbd8ed80000000 0x08fdbd8ed8000000 0x8ffffc7f80000007 0xe8ffffc7f8000000

def z941 : W := mkw 0x7b643f127ffffecf 0x07b643f127ffffec 0x7fe01f807fffffcd 0xf7fe01f807fffffc

def z942 : W := mkw 0x49e9e6a5a7cb1538 0xc49e9e6a5a7cb153 0x41e1e38187c30731 0x041e1e38187c3073

def z943 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8ffff3ff80000003 0x48ffff3ff8000000

def z944 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1e0c7e783cf8ca 0x9be1e0c7e783cf8c

def z945 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5e7fe0007fff000a 0x95e7fe0007fff000

def z946 : W := mkw 0x4ddfa01077bb41a8 0x84ddfa01077bb41a 0x5fffe0007fffc30b 0xf5fffe0007fffc30

def z947 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7fe01f807fc0ff05 0x47fe01f807fc0ff0

def z948 : W := mkw 0x2b4019002d40b606 0x02b4019002d40b60 0x1f8011807fc0fb00 0x51f8011807fc0fb0

def z949 : W := mkw 0x5004201252bf48c9 0x05004201252bf48c 0x00000000003f00c0 0x000000000003f00c

def z950 : W := mkw 0x12ad5effca66fdf5 0xc12ad5effca66fdf 0xe19d1fffc623ffff 0x6e19d1fffc623fff

def z951 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xefffffffc623c7ff 0xeefffffffc623c7f

def z952 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0xffe01f807fe0ffcf 0xfffe01f807fe0ffc

def z953 : W := mkw 0x0dfbc6a580000000 0x00dfbc6a58000000 0x8fffffff80000007 0xe8fffffff8000000

def z954 : W := mkw 0x4ddfa01077bb4088 0x04ddfa01077bb408 0xfffff271ffffc4ff 0xffffff271ffffc4f

def z955 : W := mkw 0x4ddfa00075b90008 0x04ddfa00075b9000 0x1fffe00079fc000b 0xf1fffe00079fc000

def z956 : W := mkw 0x049f200052bb0008 0x0049f200052bb000 0x5fffe0007fff000b 0xf5fffe0007fff000

def z957 : W := mkw 0x8ffbdfed80401400 0x08ffbdfed8040140 0xafffffff80003c07 0xeafffffff80003c0

def z958 : W := mkw 0x4ddfa01077bb4088 0x04ddfa01077bb408 0x7fffe0007fffc0cb 0xf7fffe0007fffc0c

def z959 : W := mkw 0x86bbdeed80000000 0x086bbdeed8000000 0x8e7ffe7f80000007 0xe8e7ffe7f8000000

def z960 : W := mkw 0x4ddfa01077bb41a8 0x84ddfa01077bb41a 0x5fffe0007fff00fb 0xf5fffe0007fff00f

def z961 : W := mkw 0xaffbdfed8840b606 0x0affbdfed8840b60 0xefffffff81c0ff0f 0xfefffffff81c0ff0

def z962 : W := mkw 0x0432464c80000000 0x00432464c8000000 0x807fee7f80000007 0xa807fee7f8000000

def z963 : W := mkw 0x4ddba000379b0008 0x04ddba000379b000 0x5fe3e0003fff000b 0xb5fe3e0003fff000

def z964 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe1e3ef8f87ff3fff 0xbe1e3ef8f87ff3ff

def z965 : W := mkw 0x86bbdfed80000000 0x086bbdfed8000000 0x801fec7f80000002 0x0801fec7f8000000

def z966 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xfe1f1c7e783ff8cf 0xffe1f1c7e783ff8c

def z967 : W := mkw 0x12243e1258fdfcdd 0x412243e1258fdfcd 0x7e601e0079fffcfd 0xf7e601e0079fffcf

def z968 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0xfffff071ffffc0ff 0xffffff071ffffc0f

def z969 : W := mkw 0x84bbc6ed80000000 0x084bbc6ed8000000 0x81ffffff80000007 0xe81ffffff8000000

def z970 : W := mkw 0x2b4019002d00a206 0x02b4019002d00a20 0x7fe01d807fc0fb0d 0xf7fe01d807fc0fb0

def z971 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1e1c7e383cf8c6 0x9be1e1c7e383cf8c

def z972 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8ffefdfe00000006 0xe8ffefdfe0000000

def z973 : W := mkw 0x0024261242ef5df9 0xc0024261242ef5df 0x61e01f8047fffffd 0xf61e01f8047fffff

def z974 : W := mkw 0x2b605f04ad40b616 0x42b605f04ad40b61 0x7fe01f81ffc0ff3d 0xf7fe01f81ffc0ff3

def z975 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0xdffff3f1ffff00ff 0xfdffff3f1ffff00f

def z976 : W := mkw 0x29e967a5a7cb173a 0xc29e967a5a7cb173 0x41e1e38187c30731 0x041e1e38187c3073

def z977 : W := mkw 0x4ddfa01077bb41a8 0x84ddfa01077bb41a 0xffffe201ffffc7ff 0xfffffe201ffffc7f

def z978 : W := mkw 0x02201e000840b404 0x002201e000840b40 0x7fe01f807fc0ff0d 0xf7fe01f807fc0ff0

def z979 : W := mkw 0x8ffbdfed82020120 0x88ffbdfed8202012 0x8fffffff86000307 0xe8fffffff8600030

def z980 : W := mkw 0x2020670680cd1e5b 0x42020670680cd1e5 0xe063ef8f81ff3fff 0xbe063ef8f81ff3ff

def z981 : W := mkw 0x22205f068844be57 0x422205f068844be5 0xa0000e0f80003cf4 0x0a0000e0f80003cf

def z982 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xfe63ee0ff9ff3cff 0xffe63ee0ff9ff3cf

def z983 : W := mkw 0x0ddf800075300000 0x00ddf80007530000 0x5fffe0007ffc000b 0xf5fffe0007ffc000

def z984 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x801fe07f802300f2 0x0801fe07f802300f

def z985 : W := mkw 0x1004201258fdfcdd 0x41004201258fdfcd 0x3000000079fcf8c8 0x13000000079fcf8c

def z986 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x5fe01f807fc0ff01 0xd5fe01f807fc0ff0

def z987 : W := mkw 0xcddfa1a177bb0008 0x0cddfa1a177bb000 0x5fffe1807fff000b 0xf5fffe1807fff000

def z988 : W := mkw 0x8f72dfed80000000 0x08f72dfed8000000 0x8e7effff80000006 0xe8e7effff8000000

def z989 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xe19c13f1c623c7fc 0x4e19c13f1c623c7f

def z990 : W := mkw 0x3f727f4ebdddbe5f 0x43f727f4ebdddbe5 0x1e62ec0e39dc3800 0x91e62ec0e39dc380

def z991 : W := mkw 0x549fa0fb52bf49e9 0x8549fa0fb52bf49e 0x801fe07f803f00f2 0x0801fe07f803f00f

def z992 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0xffffffffb9c03c0f 0xfffffffffb9c03c0

def z993 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5fffe0007fff0003 0x45fffe0007fff000

def z994 : W := mkw 0x12245e5ec864fcd5 0x412245e5ec864fcd 0xe01d1e7fc023fcff 0x6e01d1e7fc023fcf

def z995 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe1e3ee0fc7ff3cff 0xfe1e3ee0fc7ff3cf

def z996 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0x7ffefffe7fc0ff0d 0xf7ffefffe7fc0ff0

def z997 : W := mkw 0x869bd9ed80000000 0x0869bd9ed8000000 0x801ff1ff80000002 0x0801ff1ff8000000

def z998 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xc063ec0f81ff38fb 0xbc063ec0f81ff38f

def z999 : W := mkw 0x4ddba0a135990008 0x04ddba0a13599000 0x9ffff3f1b9dc0007 0xf9ffff3f1b9dc000

def z1000 : W := mkw 0x22205f068844be57 0x422205f068844be5 0x00000c0e00003800 0x000000c0e0000380

def z1001 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xa063ec0f81ff38fe 0xba063ec0f81ff38f

def z1002 : W := mkw 0xaffbdfed80401602 0x0affbdfed8040160 0x8fffffff80000707 0xe8fffffff8000070

def z1003 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x001ee07e00000000 0x0001ee07e0000000

def z1004 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x7ffff0007fffc00f 0xf7ffff0007fffc00

def z1005 : W := mkw 0xaffbdfed8840b606 0x0affbdfed8840b60 0x8fffffff80003807 0xe8fffffff8000380

def z1006 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x3fe01d807fc0fb0c 0xf3fe01d807fc0fb0

def z1007 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7fe01f807fe3fffd 0xf7fe01f807fe3fff

def z1008 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x0ffefffe00000005 0xe0ffefffe0000000

def z1009 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8f9fffff80000006 0x48f9fffff8000000

def z1010 : W := mkw 0x2b407906ad8daa5f 0x42b407906ad8daa5 0x9f83f18ffe3fc3f2 0x49f83f18ffe3fc3f

def z1011 : W := mkw 0x4ddba00035990008 0x04ddba0003599000 0x1ffee00039dc0000 0xd1ffee00039dc000

def z1012 : W := mkw 0x5b4438127fbfe8cd 0x05b4438127fbfe8c 0x7fe01c007ffff8cd 0xf7fe01c007ffff8c

def z1013 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x807fe07f80000003 0xa807fe07f8000000

def z1014 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7fe00f807fc0ff09 0x97fe00f807fc0ff0

def z1015 : W := mkw 0xcffbdfeda7020000 0x0cffbdfeda702000 0x8fffffff86000007 0xe8fffffff8600000

def z1016 : W := mkw 0x8ffbdfeda5000000 0x08ffbdfeda500000 0xffffffffffc0c70f 0xfffffffffffc0c70

def z1017 : W := mkw 0x4ddfa0a177bb0128 0x84ddfa0a177bb012 0x7ffff381ffffc73f 0xf7ffff381ffffc73

def z1018 : W := mkw 0x00006006808d0859 0x400006006808d085 0xe063ec0f81ff38ff 0xbe063ec0f81ff38f

def z1019 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1f1e7ff83cf8cf 0xfbe1f1e7ff83cf8c

def z1020 : W := mkw 0x0004001040204080 0x0000400104020408 0xe19d13f1c623c7ff 0x6e19d13f1c623c7f

def z1021 : W := mkw 0x8612d84c80000000 0x08612d84c8000000 0x8e1efc7e00000006 0xe8e1efc7e0000000

def z1022 : W := mkw 0x4ddfa0a177bb0008 0x04ddfa0a177bb000 0xdfffe071ffff000b 0xfdfffe071ffff000

def z1023 : W := mkw 0x1616185a5a36e9e5 0x81616185a5a36e9e 0xff9e1ffe7e3fffff 0xfff9e1ffe7e3ffff

def z1024 : W := mkw 0x0f725f4c80000000 0x00f725f4c8000000 0x8fffffff80000007 0xe8fffffff8000000

def z1025 : W := mkw 0x8ffbdfed8800a004 0x08ffbdfed8800a00 0x9ffffffff800c007 0xe9ffffffff800c00

def z1026 : W := mkw 0x49c9a000278b0008 0x049c9a000278b000 0x5fe3e0007fff000b 0xf5fe3e0007fff000

def z1027 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x9e1e1c7e783cf8c2 0xd9e1e1c7e783cf8c

def z1028 : W := mkw 0x82a95fed80000000 0x082a95fed8000000 0x81ffffff80000007 0xe81ffffff8000000

def z1029 : W := mkw 0x4d56a00077bb0008 0x04d56a00077bb000 0x5e7ee0007fff000a 0xf5e7ee0007fff000

def z1030 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xff9d13f1fe23c7ff 0xfff9d13f1fe23c7f

def z1031 : W := mkw 0x9ffbdfed9810a004 0x09ffbdfed9810a00 0x9fffffffb8000007 0xe9fffffffb800000

def z1032 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5fffe3807fff070b 0xf5fffe3807fff070

def z1033 : W := mkw 0xab605f4cad40b606 0x0ab605f4cad40b60 0x7fe01f8e7fc0ff0d 0xf7fe01f8e7fc0ff0

def z1034 : W := mkw 0x500420127dbde8cd 0x0500420127dbde8c 0x3000000079fcf8c8 0x13000000079fcf8c

def z1035 : W := mkw 0x0000200000890008 0x0000020000089000 0x5e63e00079ff000b 0xf5e63e00079ff000

def z1036 : W := mkw 0x2b4019002d40b606 0x02b4019002d40b60 0x7f801d807fc0ff0c 0xf7f801d807fc0ff0

def z1037 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xfe1e1c7e7e3cffce 0xffe1e1c7e7e3cffc

def z1038 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0xffe01f81ffc0fffd 0xfffe01f81ffc0fff

def z1039 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0x1ffef1f07fdcc300 0xd1ffef1f07fdcc30

def z1040 : W := mkw 0x12205eff8844fdf5 0xc12205eff8844fdf 0xa0001fff8000fff4 0x0a0001fff8000fff

def z1041 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8ffdffff80000005 0x48ffdffff8000000

def z1042 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe7ffc7e783cf8cf 0xfbe7ffc7e783cf8c

def z1043 : W := mkw 0x1612184a1814a845 0x01612184a1814a84 0x9e1e0c7e381c3802 0x99e1e0c7e381c380

def z1044 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xcfffffff80030437 0xecfffffff8003043

def z1045 : W := mkw 0x02205e068844bc55 0x402205e068844bc5 0xa0001e0f8000fcf4 0x0a0001e0f8000fcf

def z1046 : W := mkw 0x0412200010990008 0x0041220001099000 0x1e62e00039dc0000 0x91e62e00039dc000

def z1047 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7f801f807fc0ff0c 0x57f801f807fc0ff0

def z1048 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x8e1fe07f80000002 0xe8e1fe07f8000000

def z1049 : W := mkw 0x0616184a50340841 0x00616184a5034084 0xbe1e1c7e783c38ce 0xfbe1e1c7e783c38c

def z1050 : W := mkw 0x3616195a5834eac7 0x03616195a5834eac 0xbe1e1dfe783cfbce 0xfbe1e1dfe783cfbc

def z1051 : W := mkw 0x0004201242af49f9 0xc0004201242af49f 0x00000000003f00f0 0x000000000003f00f

def z1052 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x5fe3e0007fff000b 0xf5fe3e0007fff000

def z1053 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x1e62e00039fc000a 0xb1e62e00039fc000

def z1054 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xe19d13f1c603c7f5 0x4e19d13f1c603c7f

def z1055 : W := mkw 0x8ffbdfeda5000000 0x08ffbdfeda500000 0x9ffffffffe000007 0xe9ffffffffe00000

def z1056 : W := mkw 0x0416200050b90008 0x00416200050b9000 0x1e7ee00079fc000a 0xf1e7ee00079fc000

def z1057 : W := mkw 0x4d56a00075b90008 0x04d56a00075b9000 0x5e7fe00079ff000b 0xf5e7fe00079ff000

def z1058 : W := mkw 0xaffbdfedad00a206 0x0affbdfedad00a20 0xdfffffffffc0c30f 0xfdfffffffffc0c30

def z1059 : W := mkw 0xe9e9e7a5a7cb160a 0x0e9e9e7a5a7cb160 0x41e1e38187c30701 0x041e1e38187c3070

def z1060 : W := mkw 0x2be95fa5ad40b606 0x02be95fa5ad40b60 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z1061 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x1e7fe00079ff000a 0xf1e7fe00079ff000

def z1062 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1f1c7ff83ff8fe 0xfbe1f1c7ff83ff8f

def z1063 : W := mkw 0x220018002d40b606 0x0220018002d40b60 0x7f801f807fc0ff0d 0xf7f801f807fc0ff0

def z1064 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x9ffffffff800000f 0xf9ffffffff800000

def z1065 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x5e62e0007fdc0008 0x95e62e0007fdc000

def z1066 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5ffde0007fff0009 0x55ffde0007fff000

def z1067 : W := mkw 0x8ffbdfed80401400 0x08ffbdfed8040140 0xefffffff81e33cff 0xfefffffff81e33cf

def z1068 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x1fffe0007fdc0003 0xf1fffe0007fdc000

def z1069 : W := mkw 0x89e9c7a580000000 0x089e9c7a58000000 0x81ffffff80000007 0xe81ffffff8000000

def z1070 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0xefffffff87c0ff07 0xeefffffff87c0ff0

def z1071 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x801fec7f80000006 0xa801fec7f8000000

def z1072 : W := mkw 0x84bbc7ed80000000 0x084bbc7ed8000000 0x801fe3ff80000002 0x0801fe3ff8000000

def z1073 : W := mkw 0x8fdbd9ed80000000 0x08fdbd9ed8000000 0x8f9ff3ff80000007 0x68f9ff3ff8000000

def z1074 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xe19f1fffc623c7ff 0xee19f1fffc623c7f

def z1075 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0xfffc1ff07fc0ff0f 0xffffc1ff07fc0ff0

def z1076 : W := mkw 0x296007002d40b606 0x0296007002d40b60 0x7fe003807fc0ff09 0xf7fe003807fc0ff0

def z1077 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xa19d13f1c623c7f6 0x4a19d13f1c623c7f

def z1078 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0xffe11f81ffc0ff0f 0xfffe11f81ffc0ff0

def z1079 : W := mkw 0x008d00b1523241a0 0x8008d00b1523241a 0xf19d13f1fe3fc7ff 0x7f19d13f1fe3fc7f

def z1080 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xefffffff8000040f 0xeefffffff8000040

def z1081 : W := mkw 0xb2205fff8844fec7 0x0b2205fff8844fec 0xa0001fff8000ffc4 0x0a0001fff8000ffc

def z1082 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7fe21f807ffcff0f 0xf7fe21f807ffcff0

def z1083 : W := mkw 0x008d00b1422241a0 0x8008d00b1422241a 0xe1fd13f1c7e3c7ff 0xfe1fd13f1c7e3c7f

def z1084 : W := mkw 0x069b984800000000 0x0069b98480000000 0x8e1ffc7e00000006 0xe8e1ffc7e0000000

def z1085 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0xdfffec0e7fff000f 0xfdfffec0e7fff000

def z1086 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe063ff8f81ffffff 0xbe063ff8f81fffff

def z1087 : W := mkw 0x2ffb9f482d40b606 0x02ffb9f482d40b60 0xfffffffe7fc0ff0f 0xffffffffe7fc0ff0

def z1088 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5ffee0007fdc0009 0xf5ffee0007fdc000

def z1089 : W := mkw 0x0ddba00025890008 0x00ddba0002589000 0x5fffe0007fff000b 0xf5fffe0007fff000

def z1090 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x5e62e00039dc0009 0xb5e62e00039dc000

def z1091 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x0e7eec7e00000000 0x80e7eec7e0000000

def z1092 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe063ee0f81ff3cf7 0x0e063ee0f81ff3cf

def z1093 : W := mkw 0x2b4019002d40b606 0x02b4019002d40b60 0x7f8013807fc0ff0d 0x77f8013807fc0ff0

def z1094 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5e7fe00039ff000b 0xb5e7fe00039ff000

def z1095 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0x8063ee0f81ff38f7 0xb8063ee0f81ff38f

def z1096 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x81ffffff80000007 0x081ffffff8000000

def z1097 : W := mkw 0x4ddfa01077bb41a8 0x84ddfa01077bb41a 0x7ffff3807fffc7ff 0xf7ffff3807fffc7f

def z1098 : W := mkw 0x8ffbdfed8840b404 0x08ffbdfed8840b40 0xfffffffff9c0fc0f 0xffffffffff9c0fc0

def z1099 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbf9e1dfe7e3cfbce 0xfbf9e1dfe7e3cfbc

def z1100 : W := mkw 0x0ddfa00050b90008 0x00ddfa00050b9000 0x5fffe00079ff000b 0xf5fffe00079ff000

def z1101 : W := mkw 0x4ddfa01077bb4088 0x04ddfa01077bb408 0xdfffe0707fff00cb 0xfdfffe0707fff00c

def z1102 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbf9e1ffe783cf8cf 0xfbf9e1ffe783cf8c

def z1103 : W := mkw 0x4d56a00075b90008 0x04d56a00075b9000 0x1e7ee00039fc0002 0x91e7ee00039fc000

def z1104 : W := mkw 0x1004201250bd48d9 0x41004201250bd48d 0x00000000003f00f0 0x000000000003f00f

def z1105 : W := mkw 0x06325e4c80000000 0x006325e4c8000000 0x8e7efc7e00000006 0xe8e7efc7e0000000

def z1106 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x1fe2e0007fdc0000 0xd1fe2e0007fdc000

def z1107 : W := mkw 0x8ffbdfed8800a004 0x08ffbdfed8800a00 0x9fffffffb8003807 0xf9fffffffb800380

def z1108 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe063ec0f81ff3cfa 0x9e063ec0f81ff3cf

def z1109 : W := mkw 0x4d56a00077bb0008 0x04d56a00077bb000 0x1e62e00039ff0000 0x91e62e00039ff000

def z1110 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x1fffe0007fff0002 0xd1fffe0007fff000

def z1111 : W := mkw 0x849bc0ed82020120 0x8849bc0ed8202012 0xc19fe3ff86030733 0x0c19fe3ff8603073

def z1112 : W := mkw 0xaffbdfeda5401602 0x0affbdfeda540160 0xefffffff87c03f0f 0xfefffffff87c03f0

def z1113 : W := mkw 0x8ffbdf4c80000000 0x08ffbdf4c8000000 0x8ffffc7e00000007 0xe8ffffc7e0000000

def z1114 : W := mkw 0x8dfbc7ed80000000 0x08dfbc7ed8000000 0x81fff3ff80000007 0x681fff3ff8000000

def z1115 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xfe7e1c7e79fcf8cf 0xffe7e1c7e79fcf8c

def z1116 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe063fe0fc1fffcff 0xfe063fe0fc1fffcf

def z1117 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0xdfffe3f1ffff07fb 0xfdfffe3f1ffff07f

def z1118 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0xafffffff800004f7 0xeafffffff800004f

def z1119 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1e0c7e383c38ce 0xbbe1e0c7e383c38c

def z1120 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0xdfffffffffc0c707 0xedfffffffffc0c70

def z1121 : W := mkw 0x00a946a580000000 0x000a946a58000000 0x807fee7f80000007 0xa807fee7f8000000

def z1122 : W := mkw 0x8ffbdfeda5401400 0x08ffbdfeda540140 0xffffffffffc03c0f 0xfffffffffffc03c0

def z1123 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7fe11f81ffc3ff3d 0xf7fe11f81ffc3ff3

def z1124 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x7fffe2007fff040f 0xf7fffe2007fff040

def z1125 : W := mkw 0x8f72df4c80000000 0x08f72df4c8000000 0x8e7ffe7f80000007 0xe8e7ffe7f8000000

def z1126 : W := mkw 0xab60df04ad40b606 0x0ab60df04ad40b60 0x7fe0ff807fc0ff0d 0xf7fe0ff807fc0ff0

def z1127 : W := mkw 0x12205e4e8844bc55 0x412205e4e8844bc5 0xa0000e0f80003cf4 0x0a0000e0f80003cf

def z1128 : W := mkw 0x8ffbdfed80401400 0x08ffbdfed8040140 0x8fffffff81c03807 0xf8fffffff81c0380

def z1129 : W := mkw 0x8ffbdfedad00a004 0x08ffbdfedad00a00 0xffffffffffc0f80f 0xfffffffffffc0f80

def z1130 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5ffee0007fff0008 0xd5ffee0007fff000

def z1131 : W := mkw 0x32205f5e8844fed7 0x432205f5e8844fed 0xa0001fff8000fff4 0x0a0001fff8000fff

def z1132 : W := mkw 0x09cd20b167ab41a8 0x809cd20b167ab41a 0xfffff3f1ffffc7ff 0xffffff3f1ffffc7f

def z1133 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x5e62e00039ff0008 0x95e62e00039ff000

def z1134 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8fffffffc600c307 0xe8fffffffc600c30

def z1135 : W := mkw 0x8dfbc6ed80000000 0x08dfbc6ed8000000 0x8fffee7f80000007 0xe8fffee7f8000000

def z1136 : W := mkw 0x4ddfa0a177bb0008 0x04ddfa0a177bb000 0x5ffff1f07fff000b 0xf5ffff1f07fff000

def z1137 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x7fffec007fff380f 0xf7fffec007fff380

def z1138 : W := mkw 0x8fdb99e900000000 0x08fdb99e90000000 0x8ffffdfe00000007 0xe8ffffdfe0000000

def z1139 : W := mkw 0x0412200010990008 0x0041220001099000 0x5e63e00039ff000b 0xb5e63e00039ff000

def z1140 : W := mkw 0x4ddfa0a177bb0008 0x04ddfa0a177bb000 0xfffff3f1ffffc70f 0xffffff3f1ffffc70

def z1141 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8fffec7f80000003 0xe8fffec7f8000000

def z1142 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x7fffe0007fffc70b 0xf7fffe0007fffc70

def z1143 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x1fffe00039ff0003 0xf1fffe00039ff000

def z1144 : W := mkw 0x0fdb98482d00a004 0x00fdb98482d00a00 0xfffffc7e7fc0f80f 0xffffffc7e7fc0f80

def z1145 : W := mkw 0xa9e9e7a5a5c9161a 0x4a9e9e7a5a5c9161 0x41e1e38187c30731 0x041e1e38187c3073

def z1146 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x3e1e1c7e781cf80c 0xf3e1e1c7e781cf80

def z1147 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x5fe2e0003fdc0001 0x95fe2e0003fdc000

def z1148 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x5fffe0003fff0003 0x95fffe0003fff000

def z1149 : W := mkw 0x8fdbd9ed80000000 0x08fdbd9ed8000000 0x8ffff1ff80000003 0xe8ffff1ff8000000

def z1150 : W := mkw 0x4ddba000379b0008 0x04ddba000379b000 0x1fe2e0003fdc0000 0x91fe2e0003fdc000

def z1151 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xfe1e1e7e783cfccf 0xffe1e1e7e783cfcc

def z1152 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0x6063ee0f81ff3cf9 0x96063ee0f81ff3cf

def z1153 : W := mkw 0x4ddfa0a177bb0128 0x84ddfa0a177bb012 0xdffff3f1ffff073f 0xfdffff3f1ffff073

def z1154 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0x1e7ee00039dc0000 0x91e7ee00039dc000

def z1155 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe1e3ff8f81ff3cff 0xfe1e3ff8f81ff3cf

def z1156 : W := mkw 0x4ddfa0a177bb0128 0x84ddfa0a177bb012 0x5fffe1807fff030b 0xf5fffe1807fff030

def z1157 : W := mkw 0x1612184a1814a845 0x01612184a1814a84 0xbe1e1c7e383c38ce 0xfbe1e1c7e383c38c

def z1158 : W := mkw 0x8fdbd9ed80000000 0x08fdbd9ed8000000 0x8e1fe07f80000002 0x08e1fe07f8000000

def z1159 : W := mkw 0x09cd200067ab0008 0x009cd200067ab000 0x5fffe0007fff000b 0xf5fffe0007fff000

def z1160 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7fe3ff807fc0ff0f 0xf7fe3ff807fc0ff0

def z1161 : W := mkw 0xaffbdfeda5401602 0x0affbdfeda540160 0xdfffffffffc0070f 0xfdfffffffffc0070

def z1162 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x5fe01d807fc0fb09 0xf5fe01d807fc0fb0

def z1163 : W := mkw 0xaffbdfedaf42b726 0x8affbdfedaf42b72 0xffffffffffc3ff3f 0xfffffffffffc3ff3

def z1164 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0xbffffffff9c0f80f 0xfbffffffff9c0f80

def z1165 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0xdfffffffffc0380f 0xfdfffffffffc0380

def z1166 : W := mkw 0x8ffbdfed80401410 0x48ffbdfed8040141 0x8fffffff80000437 0xe8fffffff8000043

def z1167 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0x819fe07f80000003 0x6819fe07f8000000

def z1168 : W := mkw 0x4ddfa0a177bb0008 0x04ddfa0a177bb000 0xfffff3f1ffff04ff 0xffffff3f1ffff04f

def z1169 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xe07ffe7f81ff3cff 0xfe07ffe7f81ff3cf

def z1170 : W := mkw 0x849bc0ed82020120 0x8849bc0ed8202012 0x801fe07f80030032 0x0801fe07f8003003

def z1171 : W := mkw 0x8ddbc1ed80000000 0x08ddbc1ed8000000 0x819fe1ff80000002 0x0819fe1ff8000000

def z1172 : W := mkw 0x0be95fa580000000 0x00be95fa58000000 0x8fffffff80000007 0xe8fffffff8000000

def z1173 : W := mkw 0x8ffbdfed82020120 0x88ffbdfed8202012 0x8fffffff80030037 0xe8fffffff8003003

def z1174 : W := mkw 0x2b601f482d40b606 0x02b601f482d40b60 0xffe01ffe7fc0ff0d 0xfffe01ffe7fc0ff0

def z1175 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x1e62e00079dc0008 0xf1e62e00079dc000

def z1176 : W := mkw 0x4ddfa00077bb0008 0x04ddfa00077bb000 0xffffe0007fff00cf 0xfffffe0007fff00c

def z1177 : W := mkw 0x12205e4e8844bc55 0x412205e4e8844bc5 0x00000c0e00003800 0x000000c0e0000380

def z1178 : W := mkw 0x008900a100000000 0x0008900a10000000 0xe19d13f1c623c7ff 0x6e19d13f1c623c7f

def z1179 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x1fe01f807fc0fb05 0xf1fe01f807fc0fb0

def z1180 : W := mkw 0x06325e4c8840b404 0x006325e4c8840b40 0xfe7ffe7ff9c0fc0f 0xffe7ffe7ff9c0fc0

def z1181 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1e1c7e783cf8c6 0x4be1e1c7e783cf8c

def z1182 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xbe1c1c7e783cf8cc 0x5be1c1c7e783cf8c

def z1183 : W := mkw 0x4ddba00035990008 0x04ddba0003599000 0x1fe3e00039dc0001 0x91fe3e00039dc000

def z1184 : W := mkw 0x4ddfa0b177bb41a8 0x84ddfa0b177bb41a 0x5fffe0707fff000b 0xf5fffe0707fff000

def z1185 : W := mkw 0x1616185a5a36e9e5 0x81616185a5a36e9e 0xbe1e1c7e7e3cfbce 0xfbe1e1c7e7e3cfbc

def z1186 : W := mkw 0x0d56200075b90008 0x00d56200075b9000 0x5fffe0007fff000b 0xf5fffe0007fff000

def z1187 : W := mkw 0x4d52a00035990008 0x04d52a0003599000 0x1e63e00039dc0003 0xb1e63e00039dc000

def z1188 : W := mkw 0x4ddfa0a177bb0128 0x84ddfa0a177bb012 0xffffe381ffff07ff 0xfffffe381ffff07f

def z1189 : W := mkw 0x008900b1020241a0 0x8008900b1020241a 0xe19d13f18603c7f7 0x6e19d13f18603c7f

def z1190 : W := mkw 0x8ffbdfed8800a004 0x08ffbdfed8800a00 0xfffffffffe00ff0f 0xffffffffffe00ff0

def z1191 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0x9e1e1c7e383c38c6 0xf9e1e1c7e383c38c

def z1192 : W := mkw 0x049b804800000000 0x0049b80480000000 0x801fe07e00000002 0x0801fe07e0000000

def z1193 : W := mkw 0x86bbdfed80000000 0x086bbdfed8000000 0x807fffff80000007 0xa807fffff8000000

def z1194 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8ffffdff80000002 0xc8ffffdff8000000

def z1195 : W := mkw 0x1616185a5834e8c5 0x01616185a5834e8c 0xfe1e1c7e783ffcfe 0xffe1e1c7e783ffcf

def z1196 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0xffe21f8e7fc0ff0f 0xfffe21f8e7fc0ff0

def z1197 : W := mkw 0x2b4019002d40b606 0x02b4019002d40b60 0x7fe011807fc0ff09 0xf7fe011807fc0ff0

def z1198 : W := mkw 0x4ddba00035990008 0x04ddba0003599000 0x5fffe0007fdc000b 0xf5fffe0007fdc000

def z1199 : W := mkw 0x0ddb804800000000 0x00ddb80480000000 0x8fffe07e00000003 0xe8fffe07e0000000

def z1200 : W := mkw 0x8ffbdfed80000000 0x08ffbdfed8000000 0x8fffefff80000003 0x88fffefff8000000

def z1201 : W := mkw 0x8dfbc7ed80000000 0x08dfbc7ed8000000 0x807fe07f80000002 0x0807fe07f8000000

def z1202 : W := mkw 0x849bc0ed80000000 0x0849bc0ed8000000 0xe01fe27f802304ff 0x2e01fe27f802304f

def z1203 : W := mkw 0x8ffbdfed80401400 0x08ffbdfed8040140 0xcfffffff81c00407 0xecfffffff81c0040

def z1204 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xc063ee0f81ff3cf3 0x9c063ee0f81ff3cf

def z1205 : W := mkw 0x008940a580000000 0x0008940a58000000 0x801fe07f80000002 0x0801fe07f8000000

def z1206 : W := mkw 0x449fa00052bb0008 0x0449fa00052bb000 0x5e7fe00079ff000b 0xf5e7fe00079ff000

def z1207 : W := mkw 0x0ffbde4c80000000 0x00ffbde4c8000000 0x8ffffe7f80000007 0xe8ffffe7f8000000

def z1208 : W := mkw 0x2b605f04ad40b606 0x02b605f04ad40b60 0x7fe1ff81ffc0ff0d 0xf7fe1ff81ffc0ff0

def z1209 : W := mkw 0x0020660680cd1c59 0x40020660680cd1c5 0xa063ee0f81ff3cf6 0x9a063ee0f81ff3cf

def z1210 : W := mkw 0x2b601f002d40b606 0x02b601f002d40b60 0x7fe013807fc0ff09 0x57fe013807fc0ff0

def z1211 : W := mkw 0x0612584c80000000 0x00612584c8000000 0x8e1ffc7f80000006 0xe8e1ffc7f8000000

def z1212 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0xdfffffffbfc03f07 0xfdfffffffbfc03f0

def z1213 : W := mkw 0xaffbdfedad40b606 0x0affbdfedad40b60 0xbfffffffb9c0ff07 0xfbfffffffb9c0ff0

def z1214 : W := mkw 0x1004201258bde8dd 0x41004201258bde8d 0x30000000783ff8f8 0x130000000783ff8f

def z1215 : W := mkw 0x8ddbc0eda5000000 0x08ddbc0eda500000 0xdfffe07fffc0000b 0xfdfffe07fffc0000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z0,z2,z8,z5,z6]),(0,[z0,z1,z2,z4,z9,z10,z6]),(0,[z0,z1,z2,z4,z11,z5,z6]),(0,[z0,z1,z12,z2,z4,z13,z6]),(0,[z0,z1,z2,z4,z5,z14,z6])],[(0,[z0,z15,z1,z2,z4,z16,z6]),(1,[z17,z1,z2,z4,z5,z18]),(0,[z0,z1,z19,z2,z4,z5,z20])],[(0,[z0,z1,z21,z2,z4,z5,z6]),(0,[z22,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z12,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z23,z24]),(0,[z0,z1,z25,z2,z4,z5,z26]),(0,[z0,z1,z2,z4,z5,z27,z6])],[(0,[z0,z1,z2,z4,z28,z5,z6]),(0,[z0,z1,z29,z4,z5,z10,z6]),(0,[z0,z1,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z31,z4,z5,z6])],[(0,[z0,z32,z1,z2,z4,z5,z6]),(0,[z0,z1,z25,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z5,z6]),(0,[z0,z1,z33,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z34]),(0,[z0,z1,z19,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z35,z23])],[(0,[z15,z1,z36,z2,z4,z5,z6]),(0,[z37,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z38,z5,z6]),(0,[z39,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z40,z2,z4,z5,z24])],[(0,[z41,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z42,z4,z5,z20]),(0,[z17,z0,z1,z2,z4,z5,z18]),(0,[z17,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z35,z6]),(0,[z0,z1,z2,z4,z16,z6,z26]),(1,[z0,z1,z2,z4,z5,z43])]],
   [[(0,[z0,z1,z2,z44,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z45]),(0,[z46,z0,z1,z2,z4,z5,z20]),(0,[z0,z47,z29,z2,z4,z5,z6]),(0,[z0,z1,z48,z2,z4,z5,z6]),(0,[z0,z1,z49,z2,z4,z16,z6]),(0,[z50,z0,z1,z2,z4,z5,z20])],[(1,[z0,z1,z2,z51,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z52]),(0,[z0,z1,z2,z4,z16,z53,z6])],[(0,[z46,z0,z1,z2,z4,z5,z23]),(0,[z50,z0,z1,z2,z4,z5,z23])],[(0,[z54,z0,z1,z2,z4,z5,z55]),(0,[z0,z1,z2,z42,z4,z5,z6]),(0,[z17,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z56,z2,z4,z5,z6]),(0,[z57,z0,z1,z2,z4,z5,z6]),(0,[z58,z0,z1,z2,z4,z5,z23]),(0,[z0,z1,z59,z2,z4,z5,z6])],[(0,[z50,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z36,z2,z4,z5,z20]),(0,[z46,z0,z1,z2,z4,z5,z6]),(0,[z0,z47,z1,z2,z4,z60,z6]),(1,[z0,z1,z19,z2,z61,z6])],[(0,[z0,z62,z1,z2,z4,z5,z6]),(1,[z0,z1,z25,z4,z5,z26]),(0,[z63,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z64,z2,z4,z65,z6])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z66,z0,z1,z49,z2,z4,z6]),(0,[z67,z0,z2,z68,z4,z5,z6]),(0,[z0,z1,z2,z69,z4,z9,z6])],[(0,[z0,z1,z2,z3,z4,z5,z70]),(0,[z71,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z36,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z72,z5,z6]),(0,[z0,z1,z2,z73,z4,z5,z6]),(0,[z0,z1,z74,z2,z4,z5,z6]),(0,[z75,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z76,z6]),(0,[z0,z1,z2,z77,z4,z5,z6]),(0,[z0,z1,z2,z4,z16,z78,z6]),(0,[z79,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z80,z4,z5,z81]),(0,[z0,z1,z49,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z82,z5,z6]),(0,[z83,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z19,z2,z4,z61,z6])],[(0,[z54,z0,z1,z2,z51,z5,z6]),(0,[z0,z1,z2,z4,z84,z5,z6]),(0,[z0,z1,z2,z4,z85,z5,z6]),(0,[z0,z1,z2,z4,z86,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z6]),(0,[z0,z87,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z23,z88])],[(0,[z0,z1,z2,z4,z89,z9,z6]),(0,[z0,z1,z49,z2,z4,z5,z23])],[(1,[z41,z15,z2,z4,z5,z6]),(0,[z0,z1,z90,z2,z4,z5,z6])],[(0,[z0,z1,z2,z91,z4,z5,z6])],[(0,[z92,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z93,z9,z6]),(0,[z0,z1,z2,z4,z5,z94,z23])],[(0,[z0,z95,z1,z2,z4,z5,z6]),(0,[z0,z1,z96,z29,z4,z5,z6]),(0,[z0,z97,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z89,z8,z5,z6]),(0,[z0,z1,z2,z4,z98,z5,z6]),(1,[z0,z1,z2,z4,z5,z99]),(1,[z0,z1,z2,z4,z100,z6]),(0,[z0,z2,z4,z5,z101,z6,z24]),(1,[z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z94,z6]),(0,[z102,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z103,z0,z1,z2,z4,z5,z6]),(0,[z104,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z70,z6]),(0,[z105,z0,z1,z2,z4,z5,z6]),(0,[z106,z0,z1,z2,z4,z5,z6]),(0,[z107,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z108,z6])],[(0,[z109,z0,z1,z2,z4,z5,z6]),(0,[z110,z0,z1,z25,z2,z4,z5]),(0,[z0,z111,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z5,z6])],[(0,[z113,z0,z1,z2,z4,z5,z6]),(0,[z0,z114,z1,z2,z4,z5,z6]),(0,[z66,z1,z2,z4,z115,z5,z6]),(0,[z0,z1,z2,z4,z16,z61,z6]),(0,[z0,z1,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z116,z5,z6]),(0,[z0,z1,z2,z117,z4,z5,z6]),(0,[z0,z1,z118,z2,z4,z5,z13]),(0,[z0,z1,z25,z2,z4,z5,z10])],[(0,[z0,z119,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z120,z2,z4,z5,z6]),(0,[z0,z121,z1,z2,z4,z5,z6])],[(0,[z0,z122,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z16,z6])],[(0,[z123,z0,z1,z19,z2,z4,z6]),(0,[z7,z0,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z124,z125,z5,z6])],[(0,[z0,z1,z68,z4,z126,z5,z6]),(0,[z0,z47,z1,z29,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z127,z20])],[(0,[z0,z1,z2,z4,z5,z128,z24]),(1,[z0,z47,z29,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z129])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z130]),(0,[z131,z0,z1,z2,z4,z5,z34]),(0,[z0,z1,z2,z4,z5,z132,z6]),(0,[z0,z1,z133,z2,z4,z5,z6])],[(0,[z0,z1,z2,z134,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z135,z6]),(0,[z0,z1,z12,z4,z5,z13,z6]),(0,[z0,z1,z2,z4,z5,z136,z6])],[(0,[z137,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z138,z5,z6]),(0,[z0,z1,z2,z4,z5,z139,z6]),(0,[z0,z1,z2,z4,z5,z101,z128]),(0,[z0,z1,z2,z4,z16,z101,z6]),(0,[z0,z1,z2,z124,z4,z16,z6]),(0,[z0,z1,z2,z4,z125,z16,z6]),(0,[z0,z1,z2,z80,z4,z9,z6]),(0,[z0,z1,z140,z2,z80,z5,z6])],[(0,[z46,z131,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z89,z5,z6,z20]),(0,[z0,z1,z2,z4,z5,z6,z141]),(0,[z0,z1,z2,z4,z5,z6,z142]),(0,[z0,z1,z2,z4,z143,z16,z6]),(0,[z0,z1,z144,z2,z4,z9,z6]),(0,[z0,z1,z64,z2,z4,z5,z145])],[(0,[z46,z41,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z146,z5,z6]),(0,[z66,z0,z1,z12,z2,z4,z6]),(0,[z0,z1,z2,z147,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z20])],[(0,[z148,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z149,z4,z5,z6]),(0,[z0,z150,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z9,z151,z6]),(0,[z152,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z153,z2,z4,z5,z6])],[(0,[z148,z0,z1,z42,z4,z5,z6]),(0,[z154,z0,z1,z2,z4,z5,z20]),(1,[z0,z1,z2,z4,z5,z23]),(1,[z0,z1,z2,z69,z5,z23])],[(0,[z148,z0,z1,z155,z4,z5,z6]),(0,[z156,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z157]),(1,[z0,z1,z2,z4,z158,z6]),(0,[z0,z1,z140,z2,z4,z5,z20]),(0,[z0,z1,z2,z159,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z26]),(0,[z160,z0,z1,z2,z4,z5,z23])]],
   [[(1,[z0,z1,z2,z4,z5,z6]),(0,[z46,z1,z36,z2,z4,z5,z6]),(0,[z0,z161,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z162,z6]),(0,[z0,z1,z2,z4,z5,z6,z163]),(0,[z0,z1,z2,z4,z65,z5,z145])],[(1,[z0,z1,z2,z4,z72,z6]),(0,[z148,z0,z1,z2,z4,z5,z6]),(0,[z160,z0,z1,z2,z4,z5,z6]),(0,[z110,z154,z0,z1,z2,z4,z5]),(0,[z110,z0,z1,z40,z2,z4,z5]),(0,[z0,z1,z140,z2,z4,z5,z23])],[(0,[z154,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z40,z2,z4,z5,z101]),(0,[z0,z1,z2,z4,z125,z5,z20]),(0,[z0,z1,z2,z4,z5,z6,z164])],[(1,[z165,z1,z155,z4,z5,z6]),(0,[z131,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z166,z5,z6]),(0,[z0,z1,z140,z2,z4,z5,z6]),(0,[z0,z167,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z168,z4,z5,z6]),(0,[z0,z1,z2,z4,z143,z5,z20])],[(0,[z54,z0,z1,z2,z4,z5,z20]),(0,[z0,z169,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z170,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z171]),(0,[z0,z1,z2,z4,z172,z5,z6]),(0,[z0,z1,z2,z4,z125,z5,z23]),(0,[z0,z1,z2,z4,z5,z6,z173]),(0,[z0,z1,z64,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z23,z145])],[(1,[z0,z1,z2,z4,z174,z6]),(0,[z0,z1,z2,z4,z143,z5,z23])],[(0,[z54,z0,z1,z2,z4,z5,z23]),(0,[z41,z0,z36,z2,z4,z5,z6]),(0,[z0,z1,z25,z2,z4,z5,z6]),(0,[z0,z175,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z176,z4,z5,z6]),(0,[z0,z1,z64,z2,z4,z5,z23]),(0,[z0,z1,z177,z2,z4,z5,z6])],[(0,[z0,z1,z2,z178,z4,z5,z6]),(0,[z0,z1,z2,z4,z16,z6,z18]),(0,[z0,z1,z2,z4,z5,z43,z13]),(0,[z0,z1,z179,z2,z4,z5,z6]),(0,[z0,z1,z180,z2,z4,z5,z6])]],
   [[(0,[z54,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z16,z181,z6]),(0,[z0,z47,z1,z2,z4,z76,z6]),(0,[z0,z1,z2,z4,z5,z6,z182]),(0,[z0,z1,z64,z2,z4,z5,z6])],[(0,[z183,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z184,z5,z6]),(0,[z0,z1,z185,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z186,z6]),(0,[z0,z1,z2,z4,z8,z9,z6]),(0,[z0,z1,z40,z2,z4,z16,z6]),(0,[z0,z1,z2,z187,z4,z9,z6]),(1,[z0,z188,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z65,z5,z20])],[(0,[z0,z15,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z189,z6]),(0,[z67,z0,z1,z29,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z190,z6]),(0,[z0,z175,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z191,z5,z6])],[(0,[z0,z1,z2,z69,z192,z5,z6]),(0,[z0,z1,z193,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z65,z5,z23])],[(0,[z0,z194,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z195,z6]),(0,[z0,z1,z2,z4,z196,z5,z6]),(0,[z0,z1,z2,z4,z5,z23,z18]),(0,[z0,z1,z2,z4,z5,z197,z6]),(0,[z0,z1,z2,z4,z198,z9,z6]),(1,[z0,z1,z49,z4,z143,z6]),(0,[z0,z1,z2,z4,z5,z6,z199]),(0,[z0,z1,z2,z4,z5,z20,z200]),(0,[z0,z1,z2,z4,z5,z23,z20]),(0,[z201,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z65,z5,z6])],[(0,[z0,z1,z2,z202,z4,z5,z6]),(0,[z0,z203,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z60,z6]),(0,[z7,z0,z2,z4,z8,z5,z6]),(0,[z154,z0,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z204,z5,z6]),(0,[z0,z1,z2,z80,z4,z5,z205]),(0,[z206,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z207,z2,z4,z5,z6]),(0,[z0,z1,z208,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z65,z78,z6])],[(1,[z0,z1,z209,z4,z5,z6]),(0,[z0,z1,z210,z2,z4,z5,z6]),(0,[z0,z1,z2,z211,z4,z5,z6]),(0,[z212,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z16,z6]),(0,[z0,z1,z96,z2,z80,z5,z6]),(0,[z0,z1,z213,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z23,z23])]],
   [[(0,[z214,z0,z1,z2,z4,z5,z6]),(0,[z41,z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z115,z5,z6]),(0,[z0,z1,z2,z4,z215,z5,z6]),(0,[z0,z1,z216,z2,z4,z5,z6]),(0,[z0,z1,z217,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z218,z23])],[(0,[z0,z1,z2,z219,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z13,z6]),(0,[z0,z1,z49,z2,z4,z9,z6]),(0,[z0,z1,z2,z220,z4,z5,z6]),(0,[z0,z1,z40,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z23,z6])],[(0,[z0,z1,z221,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z222,z5,z6]),(0,[z0,z1,z2,z4,z223,z5,z6]),(0,[z0,z1,z25,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z224,z6]),(0,[z0,z1,z2,z4,z225,z5,z23])],[(0,[z0,z1,z226,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z227,z5,z6]),(0,[z0,z1,z2,z4,z9,z9,z6]),(0,[z0,z228,z1,z2,z4,z5,z6]),(0,[z0,z1,z229,z2,z4,z5,z6]),(0,[z0,z1,z230,z2,z4,z5,z6]),(0,[z0,z1,z40,z2,z4,z5,z23])],[(0,[z231,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z19,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z6,z232]),(0,[z0,z1,z96,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z225,z5,z6])],[(0,[z110,z0,z188,z1,z2,z4,z5]),(1,[z0,z2,z4,z9,z16,z6]),(0,[z0,z1,z40,z2,z4,z5,z6])],[(0,[z233,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z234,z5,z6]),(0,[z0,z1,z96,z2,z4,z5,z23])],[(0,[z165,z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z192,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z235,z6]),(0,[z17,z0,z1,z40,z2,z4,z5]),(0,[z0,z1,z236,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z16,z6,z24]),(0,[z0,z1,z2,z4,z5,z237,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z238,z6]),(0,[z0,z239,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z240,z4,z5,z6]),(0,[z0,z188,z1,z2,z4,z241,z6]),(0,[z0,z1,z96,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z242,z5,z6]),(1,[z0,z1,z243,z2,z4,z6]),(0,[z0,z1,z2,z4,z244,z5,z6]),(0,[z0,z1,z245,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z246,z6])],[(0,[z247,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z42,z4,z16,z6]),(1,[z0,z1,z248,z2,z4,z5]),(0,[z249,z0,z1,z2,z4,z5,z6]),(0,[z17,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z250,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z20,z171])],[(0,[z0,z1,z2,z4,z251,z5,z6]),(0,[z46,z0,z1,z2,z4,z16,z6]),(0,[z66,z0,z1,z19,z2,z4,z6]),(0,[z0,z252,z1,z2,z3,z5,z6]),(0,[z0,z252,z2,z3,z4,z5,z6]),(0,[z50,z0,z1,z2,z4,z16,z6]),(1,[z0,z1,z2,z4,z65,z78])],[(0,[z0,z1,z2,z4,z253,z5,z6]),(0,[z123,z0,z1,z2,z4,z115,z6]),(0,[z0,z47,z1,z2,z4,z5,z20]),(0,[z254,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z255,z6]),(0,[z0,z1,z2,z4,z5,z256,z6]),(0,[z0,z1,z2,z4,z5,z26,z20])],[(0,[z54,z0,z15,z2,z4,z5,z6]),(0,[z0,z1,z257,z2,z4,z5,z6]),(0,[z258,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z259,z4,z5,z6]),(0,[z0,z1,z260,z2,z4,z5,z6]),(0,[z0,z47,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z16,z16,z6]),(0,[z0,z1,z19,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z78,z6,z145])],[(0,[z0,z1,z36,z2,z4,z16,z6]),(0,[z0,z1,z261,z2,z4,z5,z6]),(0,[z0,z1,z2,z192,z4,z5,z20]),(0,[z0,z1,z2,z4,z262,z5,z6]),(0,[z0,z1,z2,z77,z4,z16,z6]),(0,[z0,z1,z25,z4,z5,z6,z26]),(0,[z0,z1,z263,z2,z4,z5,z6]),(0,[z0,z1,z64,z2,z4,z6,z145])]],
   [[(0,[z54,z41,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z264,z4,z5,z6]),(0,[z0,z47,z1,z2,z4,z5,z6]),(0,[z0,z47,z1,z2,z4,z5,z265]),(0,[z0,z1,z2,z4,z5,z6,z266]),(0,[z0,z1,z2,z4,z267,z5,z6]),(1,[z0,z1,z140,z126,z5,z6]),(0,[z0,z1,z2,z268,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z269,z6])],[(0,[z0,z1,z2,z270,z4,z5,z6]),(0,[z0,z1,z2,z192,z4,z5,z23]),(0,[z0,z1,z271,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z272,z6])],[(0,[z0,z1,z42,z68,z4,z5,z6]),(0,[z0,z273,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z192,z4,z5,z6]),(0,[z123,z0,z1,z2,z4,z181,z6]),(0,[z0,z1,z274,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z275,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z276]),(0,[z0,z1,z277,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z278,z6]),(0,[z54,z1,z36,z2,z4,z5,z6]),(0,[z0,z1,z2,z42,z4,z5,z23]),(0,[z165,z1,z155,z2,z4,z5,z6]),(0,[z17,z0,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z279,z5,z6]),(0,[z280,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z281,z5,z6])],[(1,[z0,z1,z2,z4,z5,z282]),(0,[z283,z0,z1,z2,z4,z5,z6]),(1,[z111,z1,z2,z4,z5,z6]),(1,[z39,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z284,z5,z6]),(0,[z285,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z286,z6]),(0,[z0,z1,z287,z2,z42,z4,z5]),(0,[z288,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z85,z6]),(0,[z7,z0,z1,z2,z4,z5,z289])],[(0,[z110,z0,z1,z2,z4,z5,z128])]],
   [[(0,[z0,z1,z290,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z181,z6]),(0,[z280,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z16,z291,z6]),(0,[z0,z1,z2,z4,z5,z292,z6]),(0,[z0,z1,z2,z4,z5,z24,z20]),(0,[z0,z1,z2,z4,z5,z6,z293]),(0,[z0,z1,z2,z4,z5,z6,z294])],[(0,[z0,z1,z36,z2,z4,z5,z23]),(0,[z7,z0,z1,z2,z4,z5,z99])],[(0,[z0,z1,z295,z2,z4,z5,z6]),(0,[z296,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z128,z20]),(0,[z0,z1,z2,z4,z5,z297,z20])],[(1,[z0,z1,z298,z4,z5,z6]),(0,[z0,z1,z2,z299,z4,z5,z6]),(1,[z66,z1,z2,z4,z115,z6]),(0,[z17,z0,z188,z1,z2,z4,z5]),(0,[z300,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z76,z5,z6]),(0,[z0,z1,z2,z124,z4,z9,z6]),(0,[z0,z1,z2,z4,z301,z5,z6]),(0,[z0,z302,z1,z2,z4,z5,z6])],[(0,[z54,z0,z1,z2,z4,z278,z6]),(0,[z0,z1,z303,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z34]),(0,[z0,z1,z2,z69,z89,z5,z6]),(0,[z0,z1,z2,z4,z5,z304,z6]),(1,[z0,z150,z2,z4,z16,z6]),(0,[z0,z1,z305,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z306,z20])],[(0,[z0,z1,z2,z4,z5,z307,z6]),(0,[z308,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z309,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z310])],[(0,[z311,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z128,z6]),(0,[z7,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z16,z312,z6]),(0,[z0,z1,z12,z2,z4,z143,z6])],[(0,[z0,z1,z2,z313,z4,z5,z6]),(0,[z0,z1,z314,z2,z4,z5,z6]),(0,[z110,z1,z2,z4,z5,z128,z6]),(1,[z0,z1,z2,z4,z5,z162]),(1,[z0,z1,z2,z4,z5,z289])]],
   [[(0,[z0,z1,z315,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z316,z6]),(0,[z67,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z68,z4,z5,z10,z6]),(0,[z0,z1,z2,z4,z317,z16,z6]),(0,[z0,z1,z2,z4,z5,z318,z6])],[(0,[z0,z1,z319,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z320,z5,z6]),(0,[z0,z1,z2,z321,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z322])],[(0,[z67,z0,z1,z2,z4,z5,z23]),(0,[z154,z0,z1,z2,z4,z5,z101])],[(0,[z0,z1,z323,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z16,z20])],[(0,[z131,z0,z1,z2,z4,z9,z6]),(0,[z67,z0,z1,z2,z4,z5,z6]),(0,[z324,z0,z1,z2,z4,z5,z6]),(0,[z154,z0,z1,z33,z4,z5,z6]),(1,[z0,z1,z2,z4,z325,z6]),(0,[z0,z1,z2,z4,z5,z20,z145])],[(0,[z110,z0,z1,z2,z4,z9,z6]),(0,[z0,z252,z1,z2,z4,z9,z6]),(1,[z0,z1,z2,z4,z16,z23])],[(0,[z0,z1,z326,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z327]),(0,[z0,z1,z25,z2,z4,z5,z101])],[(0,[z7,z0,z1,z328,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z24])]],
   [[(0,[z148,z0,z1,z2,z4,z16,z6]),(0,[z329,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z330,z2,z4,z5,z6])],[(0,[z331,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z257,z2,z4,z5]),(0,[z332,z0,z1,z2,z4,z5,z6]),(0,[z0,z333,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z100,z6]),(0,[z154,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z126,z5,z20]),(0,[z0,z1,z334,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z205]),(1,[z0,z1,z2,z5,z23,z20])],[(0,[z0,z335,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z336,z6]),(0,[z0,z1,z2,z4,z5,z6,z200]),(0,[z0,z337,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z338,z6]),(0,[z0,z1,z140,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z166,z16,z6]),(0,[z0,z1,z2,z4,z339,z5,z6])],[(0,[z340,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z287,z2,z4,z5]),(0,[z46,z1,z2,z192,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z341]),(0,[z0,z1,z2,z4,z126,z5,z23]),(0,[z0,z1,z342,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z343,z20]),(0,[z0,z1,z2,z4,z5,z23,z344])],[(0,[z0,z1,z2,z68,z4,z5,z6]),(0,[z345,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z346,z6]),(0,[z0,z1,z2,z4,z317,z5,z6]),(0,[z0,z1,z2,z4,z347,z5,z6]),(0,[z0,z1,z64,z40,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z282,z6]),(0,[z0,z1,z2,z4,z348,z5,z6]),(0,[z0,z1,z155,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z349,z6]),(0,[z0,z1,z25,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z126,z5,z6]),(0,[z0,z1,z2,z4,z5,z350,z6]),(0,[z0,z1,z2,z4,z351,z5,z6]),(0,[z0,z1,z2,z4,z5,z20,z20])],[(0,[z0,z1,z2,z4,z352,z5,z6]),(0,[z0,z1,z353,z2,z4,z5,z6]),(0,[z0,z354,z1,z2,z4,z5,z6])],[(0,[z54,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z9,z115,z6]),(0,[z7,z0,z1,z2,z4,z174,z6]),(0,[z0,z1,z64,z2,z4,z16,z6]),(0,[z0,z1,z2,z355,z4,z5,z6])]],
   [[(0,[z0,z1,z356,z2,z4,z5,z6]),(1,[z0,z1,z328,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z357])],[(0,[z0,z1,z155,z2,z4,z5,z6]),(0,[z123,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z18,z24]),(0,[z0,z1,z2,z4,z16,z6,z145]),(0,[z0,z1,z2,z4,z5,z23,z101]),(0,[z0,z1,z2,z358,z4,z5,z6])],[(0,[z0,z1,z209,z2,z4,z5,z6]),(0,[z148,z0,z1,z2,z4,z5,z23]),(0,[z359,z0,z1,z2,z4,z5,z6]),(0,[z66,z0,z1,z2,z4,z115,z6]),(0,[z154,z0,z188,z2,z4,z5,z6]),(0,[z0,z1,z360,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z361,z6]),(0,[z123,z0,z1,z2,z4,z5,z23]),(0,[z0,z362,z1,z2,z4,z5,z6]),(0,[z154,z0,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z363,z5,z6]),(0,[z0,z364,z1,z2,z4,z5,z6])],[(1,[z0,z1,z365,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z53,z6]),(0,[z0,z1,z2,z4,z65,z16,z6]),(0,[z0,z1,z2,z4,z5,z6,z366])],[(0,[z123,z0,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z19,z2,z4,z9,z6]),(0,[z0,z1,z25,z2,z4,z5,z20])],[(0,[z0,z1,z367,z2,z4,z5,z6]),(0,[z0,z1,z368,z2,z4,z5,z6]),(0,[z0,z1,z29,z2,z4,z5,z20]),(0,[z0,z1,z369,z2,z4,z5,z6]),(0,[z0,z1,z64,z2,z4,z5,z78])],[(0,[z0,z1,z29,z42,z4,z5,z6]),(0,[z0,z1,z2,z4,z115,z16,z6]),(0,[z0,z1,z2,z4,z5,z6,z370]),(0,[z371,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z25,z2,z4,z5,z23]),(0,[z372,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z78,z20])]],
   [[(0,[z0,z1,z373,z2,z4,z5,z6]),(0,[z0,z1,z29,z155,z4,z5,z6]),(0,[z1,z2,z4,z5,z128,z6,z18]),(0,[z0,z1,z2,z4,z5,z374,z6]),(0,[z375,z0,z1,z2,z4,z5,z6]),(0,[z376,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z55]),(0,[z148,z165,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z377,z5,z6]),(0,[z280,z0,z2,z4,z9,z5,z6]),(0,[z378,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z78,z23]),(0,[z379,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z1,z2,z4,z5,z380,z6]),(0,[z17,z0,z1,z25,z2,z4,z5]),(0,[z0,z1,z29,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z16,z6,z20])],[(0,[z0,z1,z2,z381,z4,z5,z6]),(0,[z0,z1,z2,z42,z4,z9,z6]),(0,[z17,z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z56,z2,z4,z9,z6]),(0,[z0,z1,z4,z5,z10,z6,z26]),(0,[z0,z1,z2,z4,z5,z6,z127]),(0,[z0,z382,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z5,z78,z6]),(0,[z0,z1,z2,z4,z65,z5,z78])],[(0,[z0,z1,z257,z36,z2,z4,z5]),(1,[z0,z1,z2,z4,z5,z307]),(0,[z46,z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z9,z128,z6]),(0,[z50,z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z383,z6]),(0,[z0,z1,z384,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z385,z5,z6]),(0,[z0,z382,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z16,z13,z6]),(0,[z0,z1,z386,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z387,z6])],[(0,[z0,z1,z2,z4,z5,z388,z6]),(0,[z0,z1,z326,z2,z42,z4,z6]),(0,[z0,z1,z2,z389,z4,z5,z6]),(0,[z0,z1,z390,z2,z4,z5,z6]),(0,[z0,z391,z1,z2,z4,z5,z6]),(0,[z0,z1,z392,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z20,z393])],[(0,[z0,z1,z2,z4,z115,z5,z20]),(0,[z0,z47,z1,z2,z4,z5,z162]),(0,[z0,z1,z2,z4,z5,z174,z6]),(0,[z0,z1,z96,z2,z4,z16,z6])]],
   [[(0,[z0,z1,z36,z2,z4,z9,z6]),(0,[z0,z1,z394,z2,z4,z5,z6]),(0,[z395,z0,z1,z2,z4,z5,z6]),(0,[z396,z0,z1,z2,z4,z5,z6])],[(0,[z397,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z398]),(0,[z0,z1,z2,z4,z115,z5,z23]),(0,[z0,z1,z399,z2,z4,z5,z6]),(0,[z0,z1,z2,z400,z4,z5,z6]),(0,[z401,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z402,z5,z6]),(0,[z0,z1,z2,z4,z5,z61,z20]),(0,[z0,z1,z2,z4,z403,z5,z6])],[(0,[z0,z1,z2,z4,z5,z404,z6]),(0,[z0,z1,z2,z405,z4,z5,z6]),(0,[z0,z1,z2,z4,z406,z5,z6]),(0,[z0,z1,z49,z2,z4,z13,z6]),(0,[z0,z1,z2,z4,z407,z5,z6])],[(0,[z0,z1,z2,z4,z5,z61,z23]),(1,[z0,z1,z2,z4,z5,z224])],[(0,[z0,z1,z2,z298,z4,z5,z6]),(0,[z408,z0,z1,z2,z4,z5,z6]),(0,[z7,z0,z252,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z16,z409,z6]),(0,[z0,z1,z2,z4,z5,z410,z6]),(0,[z0,z1,z411,z2,z4,z5,z6]),(0,[z0,z1,z412,z2,z4,z5,z20])],[(0,[z0,z1,z2,z4,z5,z6,z413]),(0,[z0,z1,z2,z414,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z61,z6])],[(0,[z0,z1,z2,z415,z4,z5,z6]),(0,[z0,z1,z2,z4,z416,z5,z6]),(1,[z0,z1,z2,z4,z5,z81]),(0,[z0,z417,z1,z2,z4,z5,z6])],[(0,[z0,z1,z248,z2,z42,z4,z5]),(1,[z0,z1,z2,z418,z4,z6]),(0,[z0,z1,z419,z2,z4,z5,z6]),(0,[z0,z1,z420,z2,z4,z5,z6]),(0,[z0,z47,z1,z2,z4,z16,z6]),(0,[z421,z0,z1,z2,z4,z5,z6]),(0,[z0,z252,z1,z2,z8,z5,z6]),(0,[z0,z1,z2,z4,z16,z10,z6]),(0,[z0,z1,z422,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z423,z6]),(0,[z0,z424,z1,z2,z4,z5,z6]),(0,[z0,z1,z412,z2,z4,z5,z6])],[(0,[z1,z36,z2,z4,z89,z5,z6]),(0,[z131,z0,z1,z2,z192,z5,z6]),(0,[z0,z1,z2,z4,z5,z101,z18]),(0,[z0,z1,z2,z4,z425,z9,z6]),(0,[z0,z188,z2,z4,z5,z6,z24]),(0,[z426,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z101,z20]),(0,[z0,z1,z427,z2,z4,z5,z6]),(0,[z0,z1,z2,z124,z4,z5,z224])],[(0,[z54,z0,z1,z209,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z428,z6]),(0,[z0,z1,z140,z4,z126,z5,z6])],[(0,[z148,z1,z2,z42,z4,z5,z6]),(0,[z131,z0,z1,z2,z4,z5,z307]),(0,[z0,z1,z2,z429,z4,z5,z6]),(0,[z0,z1,z2,z430,z4,z5,z6])],[(0,[z0,z1,z431,z2,z4,z5,z6]),(0,[z0,z1,z432,z2,z4,z5,z6]),(1,[z154,z0,z2,z4,z5,z101]),(0,[z0,z1,z433,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z434]),(1,[z0,z1,z2,z4,z5,z199])],[(0,[z0,z1,z2,z4,z5,z435,z6]),(0,[z436,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z101,z6]),(1,[z0,z1,z2,z4,z5,z437]),(1,[z0,z1,z144,z2,z5,z20])],[(1,[z54,z36,z2,z4,z5,z6]),(0,[z438,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z439,z5,z6]),(0,[z0,z1,z2,z4,z440,z5,z6]),(0,[z0,z1,z19,z2,z5,z61,z6])],[(0,[z0,z1,z2,z4,z5,z441,z6]),(0,[z7,z111,z1,z2,z4,z5,z6]),(0,[z7,z39,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z9,z6]),(0,[z280,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z442,z5,z6]),(0,[z443,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z444,z2,z4,z5,z6])]],
   [[(0,[z445,z0,z1,z2,z4,z5,z6]),(0,[z446,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z447,z5,z6]),(0,[z448,z0,z1,z2,z4,z5,z6]),(0,[z154,z17,z0,z1,z2,z4,z5]),(0,[z0,z449,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z85,z6]),(0,[z280,z0,z150,z2,z4,z5,z6]),(0,[z0,z1,z450,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z6,z26]),(0,[z0,z1,z451,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z145])],[(0,[z0,z1,z2,z4,z5,z452,z6]),(0,[z0,z1,z2,z4,z5,z453,z6]),(0,[z0,z1,z2,z124,z4,z5,z199])],[(0,[z0,z1,z2,z454,z4,z5,z6])],[(0,[z0,z1,z455,z2,z4,z5,z6]),(0,[z67,z0,z1,z2,z4,z316,z6]),(1,[z0,z1,z2,z4,z9,z20])],[(0,[z0,z1,z2,z4,z5,z456,z6]),(0,[z0,z188,z1,z2,z4,z5,z20])],[(0,[z54,z0,z36,z2,z4,z5,z6]),(0,[z0,z1,z12,z2,z4,z16,z6]),(1,[z0,z1,z2,z4,z9,z23]),(1,[z0,z1,z118,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z181,z20]),(0,[z457,z0,z1,z2,z4,z5,z6]),(0,[z66,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z458,z4,z5,z6]),(0,[z0,z1,z459,z2,z4,z5,z6])]],
   [[(0,[z460,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z461,z6]),(0,[z0,z1,z462,z2,z4,z5,z6]),(0,[z0,z1,z287,z2,z4,z5,z6]),(0,[z463,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z9,z5,z6]),(1,[z280,z0,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z464]),(1,[z0,z1,z2,z4,z5,z465]),(0,[z0,z1,z2,z466,z4,z5,z6])],[(0,[z148,z0,z1,z2,z4,z9,z6]),(0,[z165,z0,z1,z42,z4,z5,z6]),(0,[z467,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z115,z5,z181,z6]),(0,[z0,z1,z2,z4,z5,z181,z23]),(0,[z66,z0,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z328,z4,z5,z6]),(0,[z280,z0,z1,z2,z4,z5,z23]),(0,[z0,z188,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z468,z6]),(0,[z0,z1,z2,z4,z5,z6,z469]),(0,[z0,z1,z2,z4,z5,z470,z6])],[(0,[z165,z0,z1,z155,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z18]),(0,[z154,z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z471,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z81,z6]),(0,[z0,z1,z25,z40,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z20])],[(0,[z66,z0,z1,z2,z4,z5,z6]),(0,[z67,z0,z1,z2,z4,z16,z6]),(0,[z324,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z140,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z472]),(0,[z0,z1,z2,z4,z5,z6,z306]),(0,[z0,z1,z2,z473,z4,z5,z6])],[(0,[z165,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z474,z4,z5,z6]),(0,[z0,z188,z1,z2,z4,z190,z6]),(0,[z0,z1,z140,z2,z126,z5,z6]),(0,[z0,z1,z475,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z476,z6]),(0,[z0,z477,z1,z2,z4,z5,z6]),(0,[z0,z1,z144,z2,z5,z6,z20]),(0,[z0,z1,z478,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z465,z6]),(0,[z0,z1,z479,z2,z4,z5,z6]),(0,[z0,z1,z480,z2,z4,z5,z23])],[(0,[z0,z1,z2,z4,z481,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z1,z96,z68,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z265]),(0,[z0,z1,z25,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z125,z9,z6]),(0,[z0,z1,z2,z4,z482,z5,z6]),(0,[z0,z1,z12,z2,z4,z5,z20]),(0,[z483,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z404]),(0,[z0,z1,z2,z484,z4,z5,z6]),(0,[z0,z1,z2,z4,z143,z9,z6]),(0,[z0,z1,z480,z2,z4,z5,z6]),(0,[z0,z485,z1,z2,z4,z5,z6])]],
   [[(0,[z54,z0,z1,z2,z4,z5,z282]),(0,[z54,z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z286,z6]),(0,[z0,z1,z2,z4,z5,z486,z6]),(0,[z0,z1,z487,z2,z4,z5,z6]),(0,[z488,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z64,z2,z4,z9,z6]),(0,[z0,z1,z12,z2,z4,z5,z23])],[(0,[z0,z1,z2,z192,z3,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z489]),(0,[z0,z1,z2,z490,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z491,z23])],[(0,[z0,z1,z2,z492,z4,z5,z6]),(0,[z0,z1,z493,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z23,z6]),(0,[z0,z1,z12,z2,z4,z5,z6]),(0,[z0,z1,z494,z2,z4,z5,z6])],[(0,[z0,z1,z2,z495,z4,z5,z6]),(0,[z0,z1,z2,z68,z4,z16,z6]),(0,[z496,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z491,z6]),(0,[z0,z1,z2,z4,z5,z497,z6]),(0,[z0,z1,z2,z4,z5,z10,z20]),(0,[z0,z1,z498,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z18,z20]),(0,[z0,z1,z2,z4,z5,z409,z6]),(0,[z0,z1,z499,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z126,z16,z6]),(0,[z0,z1,z2,z4,z5,z6,z500])],[(0,[z0,z1,z2,z501,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z6,z232]),(0,[z0,z1,z2,z4,z65,z9,z6]),(0,[z0,z188,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z502,z6]),(0,[z0,z1,z2,z4,z5,z503,z6])],[(0,[z54,z0,z1,z298,z4,z5,z6]),(0,[z0,z47,z1,z68,z4,z5,z6]),(1,[z0,z1,z2,z4,z482,z6]),(0,[z0,z1,z504,z2,z4,z5,z20])],[(0,[z505,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z10,z6])]],
   [[(0,[z506,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z155,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z6,z507]),(0,[z0,z1,z508,z2,z4,z5,z6]),(0,[z0,z509,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z510,z4,z5,z6]),(0,[z154,z0,z1,z2,z4,z325,z6]),(0,[z0,z1,z2,z511,z4,z5,z6])],[(0,[z131,z0,z1,z2,z89,z5,z6]),(0,[z0,z1,z2,z4,z5,z316,z6]),(0,[z0,z1,z2,z4,z5,z6,z512]),(0,[z0,z513,z1,z2,z4,z5,z6]),(0,[z0,z1,z504,z2,z4,z5,z6]),(0,[z0,z1,z2,z69,z4,z5,z20])],[(0,[z0,z514,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z515,z5,z6]),(0,[z0,z1,z2,z68,z4,z5,z20]),(0,[z0,z1,z516,z2,z4,z5,z6]),(0,[z0,z1,z517,z2,z4,z5,z6]),(0,[z0,z1,z2,z518,z4,z5,z6]),(0,[z0,z1,z2,z4,z519,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z393]),(0,[z0,z1,z520,z2,z4,z5,z6])],[(0,[z488,z0,z1,z2,z4,z5,z6]),(0,[z123,z0,z1,z2,z4,z16,z6]),(1,[z0,z1,z2,z521,z5,z6]),(0,[z0,z1,z2,z69,z4,z5,z23])],[(1,[z522,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z523,z5,z6]),(0,[z524,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z68,z4,z5,z23]),(0,[z0,z1,z369,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z16,z20]),(0,[z0,z1,z40,z2,z4,z9,z6]),(0,[z525,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z526]),(0,[z0,z1,z2,z4,z527,z5,z6]),(0,[z0,z1,z19,z2,z4,z5,z437])],[(0,[z41,z15,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z365,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z325,z6]),(0,[z0,z1,z2,z69,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z16,z23]),(0,[z0,z1,z2,z4,z5,z528,z6]),(0,[z0,z1,z2,z4,z5,z6,z529])]],
   [[(0,[z17,z0,z1,z2,z4,z5,z128]),(1,[z0,z1,z2,z4,z530,z6]),(0,[z531,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z96,z2,z4,z9,z6]),(1,[z0,z1,z2,z4,z5,z322]),(0,[z0,z1,z12,z49,z4,z5,z6])],[(0,[z0,z1,z29,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z16,z6]),(0,[z0,z1,z96,z2,z126,z5,z6])],[(0,[z0,z1,z155,z2,z4,z5,z23]),(0,[z131,z1,z2,z4,z89,z5,z6]),(0,[z0,z1,z2,z4,z89,z5,z6]),(0,[z0,z1,z532,z2,z4,z5,z6]),(0,[z533,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z534,z6])],[(0,[z535,z0,z1,z2,z4,z5,z6])],[(0,[z1,z2,z192,z4,z89,z5,z6]),(0,[z0,z1,z2,z4,z93,z5,z6]),(0,[z0,z1,z2,z4,z536,z5,z6])],[(0,[z537,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z538,z2,z4,z5,z6]),(0,[z539,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z540,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z541]),(0,[z0,z1,z2,z4,z5,z6,z542]),(0,[z543,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z544,z5,z6]),(0,[z0,z1,z2,z4,z241,z5,z6])]],
   [[(0,[z0,z1,z545,z2,z4,z5,z6]),(0,[z0,z47,z1,z2,z4,z9,z6]),(0,[z0,z1,z19,z2,z4,z5,z465])],[(0,[z0,z1,z2,z546,z4,z5,z6]),(1,[z0,z1,z2,z192,z5,z20]),(0,[z0,z1,z2,z4,z9,z181,z6]),(0,[z0,z1,z2,z4,z406,z16,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z67,z0,z1,z68,z4,z5,z6]),(0,[z0,z252,z1,z2,z4,z5,z6]),(1,[z0,z1,z12,z4,z13,z6])],[(0,[z0,z1,z2,z192,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z547]),(0,[z0,z1,z29,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z5,z291,z6]),(0,[z0,z1,z548,z2,z4,z5,z6]),(0,[z549,z0,z1,z2,z4,z5,z20])],[(0,[z0,z1,z550,z2,z4,z5,z6]),(0,[z66,z0,z1,z2,z4,z181,z6]),(0,[z551,z0,z1,z2,z4,z5,z6]),(0,[z552,z0,z1,z2,z4,z5,z6]),(0,[z0,z150,z2,z4,z5,z16,z6]),(0,[z0,z1,z553,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z142]),(0,[z0,z1,z2,z4,z5,z554,z6]),(0,[z0,z1,z555,z2,z4,z5,z6])],[(0,[z0,z1,z556,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z557,z6]),(0,[z0,z1,z2,z80,z4,z5,z20]),(0,[z0,z1,z558,z2,z4,z5,z6]),(0,[z0,z1,z2,z125,z5,z61,z6]),(1,[z0,z1,z64,z2,z4,z145])],[(0,[z0,z1,z2,z4,z5,z6,z559]),(0,[z0,z1,z2,z4,z5,z99,z6]),(0,[z549,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z560,z2,z4,z5,z6]),(0,[z0,z1,z144,z2,z4,z5,z20])]],
   [[(0,[z0,z1,z2,z4,z561,z5,z6]),(0,[z0,z1,z562,z2,z4,z5,z6]),(0,[z280,z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z563,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z312,z6]),(0,[z564,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z565,z6]),(0,[z0,z1,z2,z4,z5,z566,z6]),(0,[z0,z1,z2,z192,z4,z5,z404]),(0,[z0,z1,z2,z80,z4,z5,z6])],[(0,[z123,z0,z1,z12,z2,z4,z6]),(0,[z0,z1,z144,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z343])],[(0,[z0,z1,z2,z567,z4,z5,z6]),(0,[z0,z1,z243,z2,z4,z5,z6]),(0,[z0,z29,z2,z68,z4,z5,z6]),(0,[z0,z1,z568,z2,z4,z5,z6]),(0,[z0,z1,z2,z569,z4,z5,z6])],[(0,[z123,z0,z1,z2,z124,z4,z6]),(1,[z110,z1,z2,z4,z5,z128]),(0,[z0,z1,z2,z4,z570,z5,z6]),(0,[z0,z1,z2,z4,z8,z16,z6]),(0,[z0,z1,z2,z571,z4,z5,z6]),(0,[z0,z150,z1,z2,z4,z5,z6]),(0,[z572,z0,z1,z2,z4,z5,z6])],[(0,[z522,z0,z1,z2,z4,z5,z6]),(0,[z573,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z574,z5,z6])],[(0,[z0,z1,z155,z68,z4,z5,z6]),(0,[z0,z1,z575,z2,z4,z5,z6]),(1,[z0,z1,z2,z576,z5,z6]),(0,[z0,z1,z450,z2,z4,z16,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z55]),(0,[z0,z1,z577,z2,z4,z5,z6]),(0,[z67,z0,z47,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z578,z16,z6]),(0,[z0,z1,z2,z4,z9,z6,z24]),(0,[z0,z1,z2,z4,z5,z135,z6]),(0,[z0,z1,z2,z4,z5,z579,z6]),(0,[z0,z1,z2,z4,z5,z580,z6]),(0,[z0,z1,z2,z4,z5,z581,z6]),(0,[z0,z1,z40,z2,z4,z65,z5]),(0,[z0,z1,z2,z4,z5,z6,z297]),(0,[z0,z1,z2,z4,z5,z6,z344])],[(0,[z0,z1,z582,z2,z4,z5,z6]),(0,[z0,z1,z248,z2,z4,z5,z6]),(0,[z123,z66,z1,z2,z4,z5,z6]),(0,[z583,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z320,z9,z6]),(0,[z0,z188,z1,z2,z4,z5,z101]),(0,[z0,z1,z19,z2,z124,z5,z6])],[(0,[z0,z1,z2,z584,z4,z5,z6]),(0,[z0,z1,z2,z521,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z585]),(0,[z586,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z23,z129])],[(0,[z0,z1,z2,z4,z5,z6,z587])],[(0,[z67,z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z151,z6])],[(0,[z0,z1,z2,z4,z5,z6,z289]),(0,[z0,z1,z2,z4,z8,z5,z20]),(0,[z0,z1,z588,z2,z4,z5,z20])],[(0,[z0,z15,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z124,z4,z125,z6])],[(0,[z0,z1,z2,z4,z5,z6,z589]),(0,[z0,z1,z25,z68,z4,z5,z6]),(0,[z0,z1,z2,z4,z8,z5,z23]),(0,[z0,z1,z2,z4,z9,z16,z6])]],
   [[(0,[z0,z15,z1,z2,z4,z5,z23]),(0,[z0,z1,z545,z2,z42,z4,z6]),(0,[z0,z1,z590,z2,z4,z5,z6]),(0,[z0,z188,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z591,z6])],[(0,[z0,z1,z2,z4,z592,z5,z6]),(0,[z41,z1,z2,z4,z89,z5,z6]),(0,[z0,z1,z243,z2,z4,z89,z6]),(0,[z123,z1,z2,z4,z5,z181,z6]),(0,[z0,z1,z29,z4,z126,z5,z6]),(0,[z0,z1,z365,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z8,z5,z6]),(0,[z0,z1,z2,z187,z4,z5,z6]),(0,[z0,z1,z588,z2,z4,z5,z6])],[(0,[z0,z15,z1,z2,z4,z5,z6]),(0,[z593,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z594,z6]),(1,[z123,z1,z2,z4,z181,z6]),(0,[z66,z0,z1,z2,z4,z16,z6]),(0,[z17,z0,z1,z2,z521,z5,z6]),(0,[z0,z1,z118,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z23,z26]),(0,[z58,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z595,z2,z4,z5,z6]),(0,[z0,z15,z1,z2,z4,z72,z6]),(0,[z165,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z596,z6])],[(0,[z41,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z68,z4,z9,z6]),(0,[z0,z1,z2,z4,z578,z5,z6]),(0,[z597,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z198,z5,z6]),(0,[z0,z1,z2,z3,z4,z5,z341]),(0,[z0,z1,z2,z4,z126,z9,z6]),(0,[z0,z1,z2,z4,z5,z598,z6])],[(0,[z41,z0,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z599,z5,z6]),(0,[z0,z600,z1,z2,z4,z5,z6]),(0,[z0,z601,z1,z2,z4,z5,z6]),(0,[z602,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z40,z2,z4,z5,z26]),(0,[z0,z1,z40,z4,z5,z10,z6]),(0,[z0,z1,z2,z4,z5,z603,z6])],[(0,[z604,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z5,z20]),(0,[z0,z1,z605,z2,z4,z5,z6]),(0,[z0,z1,z606,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z205]),(0,[z0,z607,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z608]),(0,[z609,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z41,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z418,z4,z5,z6]),(0,[z0,z1,z2,z4,z610,z5,z6]),(0,[z0,z1,z2,z611,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z423]),(0,[z0,z1,z49,z2,z4,z143,z6])],[(0,[z0,z1,z155,z2,z4,z9,z6]),(0,[z0,z1,z2,z612,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z5,z23]),(0,[z0,z1,z49,z2,z4,z5,z6])],[(1,[z0,z1,z2,z89,z5,z20]),(0,[z0,z1,z2,z613,z4,z5,z6]),(0,[z110,z17,z1,z2,z4,z5,z6]),(0,[z0,z188,z1,z2,z4,z5,z23]),(0,[z0,z1,z4,z143,z5,z13,z6]),(0,[z0,z1,z614,z2,z4,z5,z23])],[(0,[z165,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z615,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z616,z6]),(1,[z0,z252,z2,z3,z5,z6]),(0,[z0,z1,z140,z2,z4,z5,z423])],[(0,[z0,z1,z2,z4,z5,z617,z6]),(0,[z0,z1,z2,z4,z9,z78,z6]),(0,[z0,z1,z2,z4,z5,z6,z618]),(0,[z0,z1,z614,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z13,z20])],[(1,[z0,z1,z2,z546,z5,z6]),(0,[z619,z0,z1,z2,z4,z5,z6]),(0,[z165,z0,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z192,z8,z5,z6]),(0,[z123,z0,z1,z2,z4,z9,z6]),(0,[z620,z0,z1,z2,z4,z5,z23])],[(0,[z0,z1,z2,z4,z425,z5,z6]),(0,[z621,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z576,z5,z6]),(0,[z0,z1,z2,z4,z5,z23,z128]),(0,[z0,z1,z2,z4,z16,z23,z6]),(0,[z0,z1,z2,z4,z5,z622,z6]),(0,[z0,z1,z2,z4,z5,z13,z23]),(0,[z0,z1,z2,z5,z23,z6,z20]),(0,[z0,z1,z479,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z5,z88,z6]),(0,[z0,z1,z2,z4,z5,z623,z6])],[(0,[z0,z1,z624,z2,z4,z16,z6]),(1,[z0,z1,z2,z4,z241,z6]),(0,[z620,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z192,z4,z5,z142]),(0,[z0,z625,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z13,z6]),(0,[z0,z1,z2,z4,z626,z5,z6])],[(0,[z0,z1,z245,z2,z4,z5,z6])],[(0,[z0,z1,z29,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z627])],[(0,[z628,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z629,z6]),(0,[z0,z1,z630,z2,z4,z5,z6]),(0,[z0,z1,z2,z631,z4,z5,z6]),(0,[z0,z1,z2,z632,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z633]),(0,[z46,z0,z1,z2,z192,z5,z6]),(0,[z0,z1,z2,z4,z5,z634,z6]),(0,[z67,z0,z1,z2,z4,z530,z6])],[(0,[z0,z1,z2,z4,z51,z5,z6]),(0,[z54,z0,z1,z2,z546,z5,z6]),(0,[z0,z1,z2,z4,z635,z5,z6]),(0,[z0,z1,z2,z418,z4,z89,z6]),(0,[z0,z1,z2,z69,z4,z16,z6]),(0,[z0,z1,z636,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z410,z6]),(1,[z0,z1,z96,z80,z5,z6])],[(0,[z637,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z638,z2,z4,z5,z6]),(0,[z0,z1,z2,z639,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z61,z6]),(0,[z0,z1,z2,z640,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z641,z6])],[(0,[z0,z1,z642,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z643,z5,z6]),(0,[z0,z1,z2,z4,z5,z43,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z644]),(0,[z0,z1,z2,z4,z645,z5,z6]),(0,[z0,z1,z2,z646,z4,z5,z6]),(0,[z0,z1,z19,z2,z4,z125,z6])],[(0,[z0,z1,z2,z4,z89,z16,z6]),(0,[z0,z1,z2,z192,z5,z6,z20]),(0,[z0,z1,z647,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z23,z10])],[(0,[z0,z1,z2,z648,z4,z5,z6]),(0,[z66,z0,z1,z2,z124,z4,z6]),(0,[z0,z1,z624,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z649]),(0,[z650,z0,z1,z2,z4,z5,z6]),(0,[z214,z0,z1,z2,z4,z9,z6]),(0,[z154,z0,z1,z2,z4,z482,z6]),(0,[z0,z1,z2,z69,z5,z23,z6])],[(0,[z0,z252,z1,z2,z4,z100,z6]),(0,[z0,z651,z1,z2,z4,z5,z6]),(0,[z0,z1,z652,z2,z4,z5,z6])],[(0,[z17,z0,z1,z2,z576,z5,z6]),(1,[z0,z1,z2,z4,z5,z265]),(0,[z0,z1,z538,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z16,z6,z266])],[(0,[z41,z0,z15,z2,z4,z5,z6]),(1,[z0,z1,z545,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z653,z6]),(0,[z654,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z101,z6]),(0,[z0,z1,z40,z2,z4,z5,z10]),(0,[z0,z655,z1,z2,z4,z5,z6])],[(0,[z0,z1,z656,z2,z4,z5,z6]),(0,[z657,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z422,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z658,z5,z6]),(0,[z0,z1,z2,z124,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z23,z246])]],
   [[(0,[z659,z0,z1,z2,z4,z5,z6]),(0,[z660,z0,z1,z2,z4,z5,z6]),(0,[z661,z0,z1,z2,z4,z5,z6]),(0,[z123,z0,z1,z49,z2,z4,z6]),(1,[z0,z1,z2,z4,z190,z6]),(0,[z0,z1,z2,z4,z662,z5,z6]),(0,[z663,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z89,z5,z20]),(0,[z110,z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z664,z2,z4,z5,z6]),(0,[z0,z252,z1,z2,z4,z16,z6]),(0,[z0,z1,z1,z2,z4,z16,z6]),(0,[z0,z1,z140,z96,z4,z5,z6]),(0,[z0,z1,z2,z124,z4,z5,z23])],[(0,[z0,z1,z2,z4,z9,z6,z145])],[(0,[z0,z1,z2,z4,z89,z5,z23]),(0,[z0,z1,z2,z124,z4,z5,z6]),(0,[z0,z1,z2,z4,z125,z5,z6]),(0,[z665,z0,z1,z2,z4,z5,z20])],[(0,[z522,z0,z1,z36,z2,z4,z5]),(0,[z1,z155,z2,z42,z4,z5,z6]),(0,[z17,z1,z2,z4,z5,z6,z18]),(1,[z0,z1,z2,z4,z60,z6]),(0,[z0,z1,z305,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z8,z5,z6]),(0,[z0,z1,z96,z80,z4,z5,z6]),(0,[z0,z1,z2,z4,z143,z5,z6])],[(1,[z0,z1,z326,z2,z4,z6]),(1,[z131,z1,z2,z89,z5,z6]),(0,[z436,z0,z1,z2,z4,z9,z6])],[(0,[z666,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z140,z2,z4,z5,z322]),(0,[z667,z0,z1,z2,z4,z5,z6])],[(0,[z665,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z668,z4,z5,z6])]],
   [[(0,[z0,z15,z1,z2,z4,z286,z6]),(0,[z669,z0,z1,z2,z4,z5,z6]),(0,[z131,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z670,z5,z6]),(0,[z671,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z3,z89,z5,z6]),(0,[z110,z0,z1,z2,z4,z5,z18]),(0,[z110,z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z158,z5,z6]),(0,[z0,z252,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z80,z4,z16,z6]),(0,[z0,z1,z672,z2,z4,z5,z6]),(0,[z0,z673,z1,z2,z4,z5,z6]),(0,[z0,z1,z674,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z278,z5,z6]),(0,[z131,z0,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z530,z5,z6]),(0,[z0,z1,z144,z2,z4,z16,z6]),(0,[z0,z1,z49,z4,z143,z5,z6]),(0,[z0,z675,z1,z2,z4,z5,z6]),(1,[z0,z1,z40,z4,z5,z10]),(0,[z0,z1,z2,z4,z676,z5,z6])],[(0,[z0,z1,z677,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z6,z18]),(0,[z110,z0,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z16,z128,z6]),(0,[z0,z1,z2,z4,z5,z678,z6]),(1,[z67,z0,z68,z4,z5,z6]),(0,[z0,z1,z679,z2,z4,z5,z6]),(0,[z0,z252,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z9,z6,z20]),(0,[z0,z1,z2,z4,z5,z6,z680]),(0,[z0,z1,z681,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z437])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z131,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z682,z4,z5,z6]),(0,[z0,z252,z1,z2,z4,z158,z6]),(1,[z0,z1,z2,z4,z5,z70]),(0,[z0,z150,z1,z2,z4,z16,z6]),(0,[z0,z1,z25,z2,z4,z65,z5]),(0,[z0,z1,z2,z4,z683,z5,z20])],[(1,[z148,z1,z42,z4,z5,z6]),(0,[z110,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z341]),(0,[z0,z1,z2,z4,z9,z684,z6]),(0,[z0,z1,z25,z64,z2,z4,z5]),(0,[z0,z1,z685,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z238,z6]),(0,[z0,z1,z80,z4,z126,z5,z6]),(0,[z0,z1,z2,z124,z4,z61,z6])],[(0,[z0,z1,z2,z4,z5,z218,z6]),(0,[z0,z1,z2,z4,z684,z5,z6]),(0,[z0,z1,z2,z4,z5,z686,z6]),(0,[z0,z1,z687,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z688,z2,z4,z5,z6]),(1,[z0,z1,z640,z4,z5,z6]),(0,[z0,z1,z2,z4,z689,z5,z6]),(0,[z0,z1,z2,z4,z5,z690,z6]),(0,[z691,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z683,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z20]),(0,[z0,z1,z2,z692,z4,z5,z6])],[(1,[z46,z1,z2,z192,z5,z6]),(0,[z693,z0,z1,z2,z4,z5,z6]),(0,[z0,z188,z1,z2,z4,z9,z6]),(0,[z0,z1,z694,z2,z4,z5,z6])],[(0,[z695,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z696,z4,z5,z6]),(0,[z0,z1,z697,z2,z4,z5,z6]),(0,[z698,z0,z1,z2,z4,z5,z6]),(0,[z154,z0,z1,z640,z4,z5,z6]),(0,[z0,z1,z2,z699,z4,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z23])],[(0,[z66,z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z80,z4,z5,z23]),(0,[z0,z1,z2,z4,z5,z20,z163])],[(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z5,z20]),(0,[z0,z150,z1,z2,z4,z5,z20]),(0,[z0,z1,z144,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z700,z5,z6])],[(0,[z46,z0,z1,z2,z89,z5,z6]),(0,[z0,z1,z701,z2,z4,z5,z6]),(0,[z154,z0,z2,z4,z5,z101,z6])],[(0,[z702,z0,z1,z2,z4,z5,z6]),(0,[z54,z0,z1,z2,z4,z238,z6]),(0,[z0,z1,z2,z3,z4,z5,z23]),(0,[z0,z150,z1,z2,z4,z5,z23]),(0,[z0,z2,z4,z9,z5,z16,z6]),(0,[z0,z1,z2,z4,z5,z703,z6]),(0,[z0,z1,z144,z2,z69,z5,z6])],[(0,[z0,z1,z704,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z705,z6]),(0,[z0,z1,z2,z4,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z4,z5,z707]),(0,[z0,z1,z2,z4,z708,z6]),(0,[z0,z1,z2,z4,z709,z6]),(0,[z0,z1,z2,z4,z9,z710]),(0,[z0,z1,z96,z80,z5,z20])],[(0,[z0,z1,z711,z4,z5,z6]),(0,[z0,z373,z2,z4,z16,z6]),(0,[z0,z1,z248,z2,z4,z9]),(0,[z0,z1,z2,z4,z5,z712]),(0,[z667,z1,z2,z192,z5,z6]),(0,[z0,z1,z713,z2,z4,z5]),(1,[z0,z2,z4,z714,z6]),(0,[z0,z2,z4,z714,z16,z6])],[(0,[z0,z1,z715,z4,z5,z6]),(0,[z17,z1,z2,z576,z5,z18]),(0,[z0,z1,z2,z521,z16,z6]),(0,[z0,z1,z2,z4,z716,z6]),(0,[z0,z1,z717,z4,z5,z6]),(0,[z0,z1,z718,z4,z5,z6]),(0,[z0,z1,z96,z80,z5,z23])],[(0,[z0,z1,z2,z4,z719,z6]),(0,[z0,z1,z287,z68,z4,z5]),(0,[z0,z1,z2,z4,z9,z307]),(0,[z0,z1,z2,z5,z686,z20])],[(0,[z0,z720,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z721,z6]),(0,[z0,z1,z96,z80,z5,z6])],[(0,[z41,z1,z2,z51,z5,z6]),(0,[z0,z1,z2,z4,z722,z6]),(0,[z0,z1,z2,z4,z723,z6]),(0,[z0,z1,z2,z724,z4,z6]),(0,[z0,z485,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z725])],[(0,[z0,z1,z2,z4,z5,z726]),(0,[z0,z1,z2,z4,z16,z322]),(0,[z0,z1,z2,z4,z5,z727])],[(0,[z0,z1,z2,z4,z5,z728]),(0,[z0,z1,z729,z4,z5,z6]),(0,[z0,z1,z2,z4,z730,z5]),(0,[z0,z1,z2,z4,z5,z731]),(0,[z0,z601,z2,z4,z9,z6]),(0,[z1,z2,z4,z5,z128,z732]),(0,[z0,z2,z4,z16,z598,z6]),(0,[z0,z1,z422,z4,z198,z6]),(0,[z0,z1,z33,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z733]),(0,[z0,z382,z2,z4,z5,z88])]],
   [[(0,[z0,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z192,z5,z34]),(0,[z131,z1,z2,z89,z16,z6]),(1,[z1,z2,z4,z5,z732]),(0,[z620,z1,z2,z4,z5,z128]),(0,[z0,z1,z2,z4,z5,z734]),(0,[z0,z1,z2,z4,z735,z6])],[(0,[z0,z1,z2,z4,z5,z736]),(0,[z0,z1,z545,z2,z4,z20]),(0,[z0,z1,z2,z4,z737,z6]),(0,[z0,z167,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z738,z6]),(0,[z0,z1,z2,z4,z5,z739])],[(0,[z0,z1,z2,z4,z5,z23]),(0,[z0,z47,z29,z4,z60,z6]),(0,[z0,z1,z2,z4,z9,z224])],[(0,[z0,z1,z2,z4,z278,z55]),(0,[z0,z1,z545,z2,z4,z23]),(0,[z0,z1,z2,z4,z740,z6]),(0,[z0,z1,z2,z4,z158,z6]),(0,[z0,z1,z2,z4,z5,z741]),(0,[z0,z1,z2,z4,z190,z20])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z165,z1,z729,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z265]),(0,[z0,z1,z2,z4,z5,z742]),(0,[z0,z1,z2,z4,z5,z743]),(0,[z0,z1,z432,z2,z5,z20])],[(0,[z0,z1,z545,z2,z4,z6]),(0,[z0,z1,z40,z211,z4,z5]),(0,[z0,z1,z2,z4,z744,z16]),(0,[z0,z1,z2,z4,z190,z23])],[(0,[z0,z1,z2,z745,z4,z5]),(0,[z0,z1,z538,z2,z61,z6]),(0,[z0,z2,z4,z281,z9,z6]),(0,[z0,z477,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z746]),(0,[z0,z1,z19,z2,z747,z6]),(0,[z0,z1,z2,z4,z23,z748])],[(0,[z0,z1,z2,z546,z5,z749]),(0,[z165,z1,z155,z4,z5,z6]),(0,[z0,z1,z750,z2,z4,z6]),(0,[z0,z1,z2,z192,z16,z20]),(0,[z0,z1,z2,z28,z5,z20]),(0,[z0,z1,z2,z751,z5,z6]),(0,[z0,z1,z2,z4,z60,z20]),(0,[z0,z1,z96,z389,z5,z6]),(0,[z0,z1,z2,z4,z16,z752])]],
   [[(0,[z0,z1,z753,z4,z5,z6]),(0,[z0,z1,z754,z2,z4,z6]),(0,[z0,z1,z326,z2,z4,z20]),(0,[z131,z1,z2,z89,z5,z20]),(0,[z0,z1,z2,z4,z16,z341])],[(0,[z54,z257,z36,z2,z4,z5]),(0,[z41,z1,z2,z89,z5,z20]),(0,[z0,z1,z2,z4,z755,z6]),(0,[z0,z1,z2,z4,z60,z23]),(0,[z0,z1,z29,z4,z5,z162])],[(0,[z0,z1,z326,z2,z4,z23]),(0,[z131,z1,z2,z89,z5,z23]),(0,[z0,z607,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z756]),(0,[z0,z1,z2,z4,z757,z6])],[(0,[z0,z1,z2,z4,z5,z758]),(0,[z0,z1,z2,z4,z5,z759]),(0,[z7,z0,z2,z8,z5,z289]),(0,[z0,z1,z640,z4,z16,z6]),(0,[z0,z1,z2,z4,z9,z199]),(0,[z0,z1,z2,z4,z5,z760])],[(0,[z0,z1,z2,z4,z5,z761]),(0,[z0,z1,z762,z2,z5,z6]),(0,[z0,z1,z326,z2,z4,z6]),(0,[z131,z1,z2,z89,z5,z6]),(0,[z46,z1,z2,z192,z16,z6]),(0,[z0,z1,z763,z4,z5,z6])],[(0,[z54,z36,z2,z4,z5,z282]),(0,[z54,z36,z2,z4,z9,z6]),(0,[z1,z36,z2,z89,z5,z20]),(0,[z0,z188,z2,z4,z5,z24]),(0,[z0,z1,z25,z4,z5,z276])],[(0,[z67,z0,z68,z4,z5,z20]),(0,[z7,z0,z2,z8,z5,z99]),(0,[z0,z1,z588,z4,z5,z343])],[(0,[z0,z1,z2,z4,z5,z764]),(0,[z0,z765,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z766]),(0,[z0,z1,z2,z4,z5,z767]),(0,[z0,z1,z2,z4,z5,z768])]],
   [[(0,[z0,z1,z2,z4,z769,z6]),(0,[z0,z1,z2,z592,z5,z20]),(0,[z148,z1,z42,z4,z5,z20]),(0,[z0,z770,z1,z2,z4,z5]),(0,[z67,z0,z68,z4,z5,z23]),(0,[z0,z1,z2,z4,z5,z771]),(0,[z0,z188,z2,z4,z190,z24]),(0,[z0,z1,z80,z772,z5,z6]),(0,[z0,z1,z2,z4,z773,z6]),(0,[z0,z1,z2,z4,z774,z23])],[(0,[z0,z1,z2,z4,z238,z20]),(0,[z0,z1,z2,z775,z4,z6]),(0,[z0,z1,z2,z250,z5,z20]),(0,[z0,z451,z2,z4,z16,z6]),(0,[z0,z1,z40,z4,z5,z292]),(0,[z0,z1,z40,z4,z5,z10])],[(0,[z0,z1,z2,z776,z4,z6]),(0,[z0,z1,z2,z567,z5,z20]),(0,[z148,z1,z42,z4,z5,z23]),(0,[z0,z1,z2,z4,z5,z777]),(0,[z0,z1,z2,z4,z5,z778]),(0,[z67,z0,z68,z4,z5,z6]),(0,[z0,z1,z2,z4,z774,z6]),(0,[z0,z1,z4,z5,z10,z779]),(0,[z0,z1,z2,z4,z780,z23]),(0,[z0,z1,z2,z4,z65,z781])],[(0,[z54,z36,z298,z4,z5,z6]),(0,[z0,z1,z2,z4,z238,z23]),(0,[z0,z1,z2,z782,z5,z6]),(0,[z436,z1,z2,z4,z115,z6]),(0,[z0,z1,z2,z4,z783,z6]),(0,[z0,z1,z2,z4,z5,z70]),(0,[z7,z0,z2,z8,z16,z6]),(0,[z324,z1,z2,z4,z312,z6]),(0,[z1,z2,z4,z16,z784,z6]),(0,[z0,z1,z2,z5,z23,z357]),(0,[z0,z1,z64,z2,z4,z781])],[(0,[z148,z1,z42,z4,z5,z6]),(0,[z0,z1,z785,z4,z5,z6]),(0,[z0,z1,z2,z4,z780,z6]),(0,[z0,z1,z2,z4,z9,z423])],[(0,[z0,z1,z2,z4,z238,z6]),(0,[z0,z1,z786,z2,z4,z6]),(0,[z0,z1,z2,z576,z16,z6]),(0,[z0,z1,z2,z4,z5,z787]),(0,[z0,z1,z2,z4,z788,z6])],[(0,[z0,z1,z2,z4,z16,z55]),(0,[z0,z1,z2,z4,z789,z6]),(0,[z46,z1,z2,z192,z5,z23]),(0,[z0,z790,z68,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z791])],[(0,[z0,z1,z792,z2,z4,z6]),(0,[z0,z1,z2,z610,z5,z20]),(0,[z0,z1,z2,z4,z793,z6]),(0,[z0,z252,z2,z3,z9,z6]),(0,[z0,z1,z422,z4,z143,z6]),(0,[z0,z1,z2,z4,z9,z465])]],
   [[(0,[z0,z1,z2,z546,z278,z6]),(0,[z0,z1,z2,z4,z5,z794]),(0,[z0,z1,z49,z4,z578,z6]),(0,[z0,z795,z2,z4,z5,z6])],[(0,[z1,z2,z729,z4,z5,z6]),(0,[z0,z1,z243,z2,z4,z20]),(0,[z0,z1,z2,z4,z5,z796]),(0,[z0,z1,z2,z4,z5,z797]),(0,[z0,z2,z4,z9,z16,z6]),(0,[z0,z2,z466,z4,z16,z6]),(0,[z154,z0,z2,z4,z482,z101]),(0,[z0,z1,z2,z4,z798,z6])],[(0,[z0,z1,z799,z2,z5,z6]),(0,[z0,z1,z800,z2,z4,z5]),(0,[z0,z1,z2,z4,z16,z801])],[(0,[z0,z1,z2,z4,z802,z6]),(0,[z0,z1,z243,z2,z4,z23]),(0,[z0,z188,z271,z2,z4,z5]),(0,[z0,z1,z2,z4,z76,z162]),(0,[z0,z1,z140,z772,z5,z6])],[(0,[z0,z1,z2,z51,z16,z6]),(0,[z0,z1,z2,z803,z5,z6]),(0,[z0,z1,z2,z4,z804,z6]),(0,[z0,z1,z2,z4,z805,z6]),(0,[z7,z0,z328,z8,z5,z6]),(0,[z0,z673,z2,z4,z16,z6]),(0,[z0,z188,z2,z4,z5,z88])],[(0,[z0,z1,z243,z2,z4,z6]),(0,[z7,z0,z2,z8,z5,z23]),(0,[z0,z1,z2,z16,z23,z20]),(0,[z0,z1,z2,z4,z5,z806])],[(0,[z0,z1,z807,z4,z5,z6]),(0,[z0,z1,z2,z4,z808,z6]),(0,[z0,z1,z2,z4,z9,z404]),(0,[z0,z1,z809,z2,z16,z6])],[(0,[z148,z1,z248,z42,z4,z5]),(0,[z0,z1,z810,z4,z5,z6]),(0,[z0,z1,z2,z811,z5,z6]),(0,[z0,z1,z2,z4,z65,z78])]],
   [[(0,[z0,z1,z812,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z813]),(0,[z0,z1,z2,z648,z5,z20]),(0,[z17,z1,z2,z4,z5,z18]),(0,[z0,z161,z2,z4,z5,z24]),(0,[z0,z1,z25,z4,z5,z327]),(0,[z0,z1,z25,z4,z16,z26]),(0,[z0,z1,z140,z126,z5,z20]),(0,[z0,z1,z2,z4,z814,z6]),(0,[z0,z1,z2,z4,z5,z815]),(0,[z0,z1,z2,z4,z225,z78])],[(0,[z0,z1,z2,z89,z5,z34]),(0,[z0,z333,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z816,z6]),(0,[z0,z1,z817,z4,z5,z6]),(0,[z0,z1,z118,z2,z4,z16])],[(0,[z0,z1,z2,z4,z5,z818]),(0,[z0,z1,z2,z4,z5,z819]),(0,[z0,z1,z140,z126,z5,z23]),(1,[z0,z1,z2,z5,z820])],[(0,[z0,z1,z33,z4,z5,z101])],[(0,[z0,z1,z821,z4,z5,z6]),(0,[z0,z1,z822,z4,z5,z6]),(0,[z7,z0,z2,z8,z174,z6]),(0,[z0,z1,z140,z126,z5,z6]),(0,[z0,z1,z2,z4,z5,z823])],[],[(0,[z0,z1,z2,z51,z5,z23]),(0,[z0,z1,z2,z4,z286,z20]),(0,[z0,z824,z1,z2,z4,z5]),(0,[z0,z47,z29,z4,z76,z6]),(0,[z0,z1,z2,z4,z5,z43])],[(0,[z0,z1,z261,z2,z5,z20]),(0,[z0,z1,z2,z4,z9,z825]),(0,[z0,z1,z19,z2,z61,z20])]],
   [[(0,[z0,z1,z2,z4,z278,z6]),(0,[z0,z1,z826,z2,z4,z6]),(0,[z46,z1,z2,z299,z5,z6]),(0,[z0,z1,z2,z89,z16,z20]),(0,[z0,z1,z4,z5,z6,z827]),(0,[z0,z828,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z829]),(0,[z0,z1,z2,z4,z5,z830]),(0,[z0,z1,z2,z643,z5,z23]),(0,[z0,z1,z2,z4,z5,z831]),(0,[z0,z1,z12,z4,z43,z13]),(0,[z0,z1,z2,z4,z832,z6])],[(0,[z111,z1,z2,z4,z5,z6]),(0,[z0,z833,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z834]),(0,[z154,z0,z2,z4,z5,z725]),(0,[z0,z1,z2,z4,z5,z835]),(0,[z0,z1,z19,z2,z61,z23])],[(0,[z0,z1,z2,z4,z286,z6]),(0,[z110,z228,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z16,z99]),(0,[z7,z0,z2,z811,z5,z6]),(0,[z0,z1,z2,z4,z836,z6]),(0,[z0,z1,z19,z2,z410,z6]),(0,[z0,z1,z480,z4,z5,z491])],[(0,[z0,z1,z2,z546,z16,z6]),(0,[z0,z1,z2,z4,z837,z6]),(0,[z0,z1,z2,z521,z9,z6]),(0,[z0,z1,z838,z4,z5,z6]),(0,[z0,z1,z19,z2,z61,z6])],[(0,[z0,z1,z2,z4,z839,z5]),(0,[z308,z0,z2,z8,z5,z6]),(0,[z0,z1,z2,z4,z840,z6])],[(0,[z0,z1,z841,z2,z4,z6]),(0,[z426,z1,z2,z4,z5,z128]),(0,[z0,z1,z2,z4,z842,z6]),(0,[z843,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z844]),(0,[z154,z0,z2,z4,z5,z306])],[(0,[z0,z1,z2,z4,z5,z845]),(0,[z0,z1,z846,z4,z5,z6]),(0,[z0,z1,z538,z2,z16,z20])],[(0,[z0,z1,z847,z2,z4,z5]),(0,[z0,z1,z2,z4,z848,z6]),(0,[z0,z1,z2,z4,z5,z849]),(0,[z0,z1,z2,z4,z9,z322])]],
   [[(0,[z0,z1,z2,z4,z850,z6]),(0,[z0,z1,z790,z4,z5,z6]),(0,[z851,z0,z1,z2,z4,z5]),(0,[z154,z0,z640,z4,z5,z101])],[(0,[z0,z1,z209,z4,z5,z55]),(0,[z0,z1,z2,z4,z5,z852]),(0,[z109,z1,z2,z89,z5,z6]),(0,[z0,z1,z2,z4,z5,z853]),(0,[z0,z477,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z854,z6])],[(0,[z41,z15,z2,z4,z5,z6]),(0,[z0,z1,z855,z2,z4,z5]),(0,[z0,z1,z2,z521,z5,z404]),(0,[z0,z1,z33,z4,z5,z20]),(0,[z0,z1,z856,z2,z4,z5])],[(0,[z41,z15,z2,z4,z72,z6]),(0,[z0,z1,z2,z4,z5,z162]),(0,[z0,z1,z2,z4,z5,z289]),(0,[z0,z1,z96,z80,z16,z6])],[(0,[z0,z1,z2,z4,z5,z857]),(0,[z0,z1,z2,z4,z100,z23]),(0,[z0,z1,z2,z858,z16,z6]),(0,[z0,z1,z33,z4,z5,z23])],[(0,[z0,z1,z2,z4,z5,z859]),(0,[z0,z1,z96,z80,z5,z205]),(0,[z0,z1,z2,z4,z5,z781])],[(0,[z0,z1,z2,z4,z860,z6]),(0,[z0,z1,z861,z4,z5,z6]),(0,[z1,z862,z2,z4,z5,z6]),(0,[z0,z1,z2,z863,z5,z6]),(0,[z0,z1,z2,z4,z864,z6]),(0,[z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z99]),(0,[z691,z0,z2,z4,z9,z6]),(0,[z0,z364,z2,z4,z9,z6])],[(0,[z0,z1,z209,z51,z5,z6]),(0,[z0,z1,z2,z4,z5,z865]),(0,[z0,z1,z2,z4,z16,z20]),(0,[z0,z1,z64,z2,z4,z269])]],
   [[(0,[z862,z36,z2,z4,z5,z6]),(0,[z522,z0,z1,z2,z4,z16]),(0,[z131,z1,z2,z89,z5,z34]),(0,[z0,z1,z2,z192,z9,z20]),(0,[z0,z1,z2,z4,z5,z866]),(0,[z0,z1,z2,z4,z325,z6]),(0,[z0,z1,z2,z4,z5,z867]),(0,[z102,z0,z2,z4,z9,z6]),(0,[z0,z1,z2,z191,z5,z23])],[(0,[z868,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z9,z341]),(0,[z0,z1,z2,z4,z16,z23])],[(0,[z0,z1,z2,z4,z6,z869]),(0,[z0,z1,z2,z4,z60,z162]),(0,[z0,z47,z29,z4,z5,z20]),(0,[z0,z1,z2,z4,z65,z151])],[(0,[z0,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z870]),(0,[z0,z1,z2,z4,z16,z265]),(0,[z0,z1,z2,z4,z174,z99])],[(0,[z0,z1,z2,z4,z9,z142]),(0,[z871,z0,z1,z2,z4,z5]),(0,[z0,z47,z29,z4,z5,z23]),(0,[z0,z1,z640,z4,z9,z6])],[(0,[z0,z1,z257,z2,z4,z5]),(0,[z46,z1,z2,z192,z9,z6]),(0,[z0,z188,z2,z4,z5,z725]),(0,[z0,z1,z2,z4,z5,z205])],[(0,[z165,z1,z155,z4,z16,z6]),(0,[z0,z1,z2,z5,z218,z20]),(0,[z0,z1,z12,z415,z4,z6]),(0,[z0,z47,z29,z4,z5,z6]),(0,[z0,z1,z2,z4,z872,z6]),(0,[z0,z47,z29,z4,z5,z265]),(0,[z0,z433,z2,z4,z9,z6]),(0,[z0,z1,z2,z692,z5,z23])],[(0,[z0,z1,z287,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z873]),(0,[z0,z1,z2,z4,z874,z6]),(0,[z0,z1,z875,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z876]),(0,[z0,z1,z25,z4,z5,z344]),(0,[z0,z1,z877,z4,z5,z20])]],
   [[(0,[z0,z1,z2,z858,z5,z6]),(0,[z148,z1,z287,z42,z4,z5]),(0,[z0,z1,z878,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z879]),(0,[z0,z2,z4,z5,z6,z880]),(0,[z0,z1,z2,z4,z5,z820]),(0,[z0,z1,z2,z4,z881,z20]),(0,[z0,z1,z2,z69,z5,z820])],[(0,[z0,z1,z882,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z883]),(0,[z17,z1,z133,z2,z4,z5]),(0,[z67,z0,z68,z4,z316,z6]),(0,[z0,z1,z2,z4,z5,z884]),(0,[z0,z1,z2,z4,z158,z20]),(0,[z0,z1,z885,z2,z4,z5])],[(0,[z0,z1,z877,z4,z5,z6]),(0,[z0,z1,z762,z2,z16,z6]),(0,[z0,z1,z2,z4,z886,z6])],[(0,[z1,z36,z2,z51,z5,z6]),(0,[z0,z1,z2,z4,z72,z20]),(0,[z0,z1,z2,z4,z887,z6]),(0,[z17,z1,z360,z2,z4,z5]),(0,[z110,z1,z2,z4,z9,z128]),(0,[z888,z0,z1,z2,z4,z5]),(0,[z597,z0,z68,z4,z5,z6]),(0,[z0,z1,z328,z4,z5,z6]),(0,[z7,z0,z2,z8,z9,z6]),(0,[z0,z1,z2,z4,z158,z23]),(0,[z0,z188,z2,z4,z16,z24])],[(0,[z0,z273,z2,z3,z5,z6]),(0,[z7,z0,z2,z8,z85,z6]),(0,[z0,z1,z118,z2,z4,z9]),(0,[z0,z1,z2,z69,z5,z23]),(0,[z0,z1,z889,z4,z5,z20])],[(0,[z0,z1,z209,z546,z5,z6]),(0,[z0,z1,z2,z546,z5,z890]),(0,[z0,z1,z891,z2,z4,z5]),(0,[z0,z1,z2,z4,z72,z23]),(0,[z165,z1,z155,z4,z5,z20]),(0,[z0,z1,z2,z576,z9,z6]),(0,[z7,z39,z2,z8,z5,z6])],[(0,[z0,z1,z2,z4,z9,z55]),(0,[z0,z1,z2,z4,z892,z6]),(0,[z0,z1,z2,z4,z5,z893]),(0,[z0,z1,z2,z4,z5,z894]),(0,[z0,z1,z4,z143,z895,z6]),(0,[z0,z1,z25,z473,z4,z5]),(0,[z0,z1,z2,z4,z896,z6])]],
   [[(0,[z0,z1,z2,z4,z72,z6]),(0,[z165,z1,z155,z4,z5,z23]),(0,[z1,z2,z192,z89,z5,z20]),(0,[z0,z1,z2,z4,z897,z6]),(0,[z0,z1,z2,z4,z5,z898]),(0,[z0,z354,z29,z4,z5,z6]),(0,[z0,z1,z2,z4,z174,z20]),(0,[z0,z1,z40,z4,z16,z10]),(0,[z0,z1,z2,z5,z20,z164])],[(0,[z0,z577,z2,z4,z16,z6]),(0,[z67,z0,z68,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z899]),(0,[z0,z1,z889,z4,z5,z6]),(0,[z214,z1,z2,z4,z684,z6])],[(0,[z0,z1,z2,z4,z174,z23]),(0,[z0,z1,z2,z4,z16,z70]),(0,[z0,z1,z2,z4,z5,z900]),(0,[z0,z1,z40,z4,z5,z343]),(0,[z0,z1,z901,z4,z5,z20])],[(0,[z0,z1,z2,z4,z5,z902]),(0,[z148,z1,z42,z4,z16,z6]),(0,[z0,z1,z2,z4,z903,z6]),(0,[z0,z1,z640,z4,z325,z6])],[(0,[z0,z1,z2,z51,z278,z6]),(0,[z0,z1,z2,z4,z174,z6]),(0,[z0,z1,z56,z2,z410,z6]),(0,[z0,z1,z2,z355,z5,z23])],[(0,[z0,z1,z298,z4,z5,z55]),(0,[z0,z1,z2,z51,z9,z6]),(0,[z0,z1,z2,z51,z5,z282])],[(0,[z15,z862,z2,z4,z5,z6]),(0,[z0,z1,z904,z4,z5,z6]),(0,[z0,z1,z901,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z905]),(0,[z0,z1,z2,z4,z5,z906]),(0,[z0,z1,z2,z4,z5,z907])]],
   [[(0,[z0,z1,z2,z4,z908,z5]),(0,[z0,z1,z2,z4,z5,z909]),(0,[z66,z1,z2,z4,z721,z6]),(0,[z249,z0,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z910,z6]),(0,[z0,z1,z49,z4,z143,z20])],[(0,[z0,z1,z2,z5,z911,z20]),(0,[z488,z1,z2,z4,z317,z6]),(0,[z0,z1,z25,z4,z9,z26])],[(0,[z0,z1,z209,z4,z5,z20]),(0,[z0,z1,z912,z2,z4,z9]),(0,[z0,z2,z4,z5,z725,z6]),(0,[z0,z1,z4,z772,z5,z6]),(0,[z0,z1,z96,z80,z5,z81]),(0,[z0,z1,z49,z4,z143,z23])],[(0,[z0,z1,z298,z51,z5,z6]),(0,[z0,z1,z369,z2,z4,z266]),(0,[z0,z1,z2,z4,z9,z913]),(1,[z0,z2,z4,z5,z725]),(0,[z0,z1,z2,z5,z820,z20])],[(0,[z0,z1,z2,z4,z914,z6]),(0,[z0,z1,z209,z4,z5,z23]),(0,[z0,z169,z2,z4,z16,z6]),(0,[z0,z1,z915,z4,z5,z6]),(0,[z0,z1,z2,z4,z916,z6]),(0,[z0,z1,z2,z917,z5,z6]),(0,[z0,z1,z49,z4,z143,z6])],[(0,[z0,z1,z2,z51,z5,z852]),(0,[z0,z1,z2,z4,z918,z6]),(0,[z1,z303,z2,z89,z5,z6]),(0,[z919,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z920,z23])],[(0,[z0,z1,z209,z4,z5,z6]),(0,[z0,z921,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z922])],[(0,[z0,z1,z2,z418,z4,z20]),(0,[z17,z1,z2,z4,z16,z18]),(0,[z0,z1,z923,z4,z5,z6]),(0,[z0,z1,z2,z4,z920,z6]),(0,[z0,z1,z812,z4,z16,z6]),(0,[z436,z1,z2,z4,z425,z6])]],
   [[(0,[z41,z15,z2,z4,z286,z6]),(0,[z131,z1,z2,z89,z5,z307]),(0,[z0,z1,z2,z4,z924,z6]),(0,[z0,z1,z2,z4,z5,z925]),(0,[z0,z2,z4,z9,z16,z20])],[(0,[z0,z1,z2,z926,z5,z6]),(0,[z0,z927,z2,z4,z5,z6]),(0,[z0,z1,z2,z89,z9,z20])],[(0,[z0,z1,z2,z4,z5,z749]),(0,[z0,z2,z4,z9,z16,z23]),(0,[z0,z1,z2,z4,z9,z928]),(0,[z0,z1,z2,z929,z5,z6]),(0,[z0,z1,z2,z4,z5,z81]),(0,[z0,z1,z2,z4,z798,z23])],[(0,[z0,z1,z2,z4,z5,z930]),(0,[z0,z1,z2,z418,z4,z6]),(0,[z0,z1,z2,z4,z931,z6]),(0,[z111,z1,z2,z4,z5,z99]),(0,[z39,z1,z2,z4,z5,z99]),(0,[z0,z1,z140,z126,z16,z6]),(0,[z0,z2,z4,z16,z6,z366]),(0,[z0,z1,z25,z4,z5,z489])],[(0,[z0,z1,z2,z546,z9,z6]),(0,[z0,z1,z2,z546,z5,z282]),(0,[z522,z0,z1,z2,z4,z9]),(0,[z0,z1,z2,z4,z932,z6]),(0,[z1,z729,z42,z4,z5,z6]),(0,[z0,z1,z2,z4,z933,z5]),(0,[z657,z1,z2,z89,z5,z6]),(0,[z0,z1,z2,z4,z85,z99]),(0,[z0,z1,z2,z4,z934,z6])],[(0,[z0,z1,z2,z4,z16,z43]),(0,[z0,z520,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z935]),(0,[z0,z1,z936,z4,z5,z20])],[(0,[z0,z1,z2,z937,z4,z6]),(0,[z0,z1,z2,z4,z5,z938]),(0,[z0,z2,z4,z5,z725,z24])],[(1,[z1,z2,z4,z721,z6]),(0,[z0,z1,z2,z4,z939,z6]),(0,[z0,z354,z2,z4,z5,z101]),(0,[z0,z1,z2,z4,z5,z940]),(0,[z0,z1,z2,z4,z5,z941]),(0,[z0,z1,z2,z5,z108,z20])]],
   [[(0,[z0,z1,z4,z942,z5,z6]),(0,[z0,z1,z2,z4,z5,z943]),(0,[z111,z1,z2,z4,z16,z6]),(0,[z0,z1,z944,z4,z5,z6]),(0,[z0,z1,z2,z4,z945,z6]),(0,[z154,z0,z2,z4,z5,z101]),(0,[z0,z1,z2,z5,z747,z6])],[(0,[z0,z1,z2,z4,z946,z6]),(0,[z0,z1,z2,z947,z5,z6]),(0,[z0,z1,z248,z2,z4,z5]),(0,[z0,z1,z2,z948,z5,z6]),(0,[z0,z1,z2,z4,z5,z949]),(0,[z0,z1,z2,z4,z5,z437]),(0,[z0,z1,z936,z4,z5,z6]),(0,[z0,z1,z144,z2,z5,z20])],[(0,[z0,z1,z298,z546,z5,z6]),(1,[z1,z729,z4,z5,z6]),(0,[z0,z1,z772,z126,z5,z6])],[(0,[z0,z1,z2,z4,z6,z748]),(0,[z7,z0,z365,z8,z5,z6])],[(0,[z0,z1,z950,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z951]),(0,[z0,z1,z260,z126,z5,z6]),(0,[z843,z1,z2,z4,z16,z6]),(0,[z0,z1,z96,z80,z9,z6]),(0,[z0,z1,z2,z772,z5,z6])],[(0,[z0,z1,z96,z772,z5,z6])],[(0,[z0,z1,z2,z952,z5,z6]),(0,[z0,z1,z953,z2,z4,z5]),(0,[z0,z1,z2,z4,z954,z6]),(0,[z0,z1,z2,z4,z955,z6])],[(0,[z0,z1,z209,z4,z238,z6]),(0,[z0,z1,z2,z4,z278,z20]),(0,[z0,z1,z479,z2,z4,z129])]],
   [[(0,[z0,z1,z956,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z957]),(0,[z0,z1,z2,z4,z958,z6]),(0,[z111,z1,z2,z4,z5,z20]),(0,[z39,z1,z2,z4,z5,z20]),(0,[z0,z1,z2,z4,z9,z20]),(0,[z0,z1,z504,z4,z5,z26])],[(0,[z0,z1,z2,z4,z278,z23]),(0,[z41,z15,z2,z4,z16,z6]),(0,[z0,z1,z2,z348,z5,z20]),(0,[z110,z1,z2,z4,z5,z297]),(0,[z0,z1,z2,z4,z85,z20]),(0,[z0,z2,z4,z811,z5,z6]),(0,[z0,z1,z2,z4,z895,z6]),(0,[z0,z1,z459,z2,z5,z20])],[(0,[z0,z1,z2,z4,z5,z959]),(0,[z131,z1,z243,z2,z89,z6]),(0,[z0,z1,z25,z2,z576,z5]),(0,[z0,z1,z638,z2,z5,z20]),(0,[z0,z1,z2,z4,z16,z162]),(0,[z111,z1,z2,z4,z5,z23]),(0,[z39,z1,z2,z4,z5,z23]),(0,[z0,z1,z2,z4,z16,z289]),(0,[z0,z1,z2,z4,z9,z23]),(0,[z0,z1,z33,z4,z325,z6]),(0,[z0,z1,z2,z4,z960,z20])],[(0,[z0,z1,z2,z4,z286,z23]),(0,[z0,z1,z2,z4,z5,z961]),(0,[z0,z1,z2,z4,z85,z23]),(0,[z0,z1,z2,z220,z5,z23]),(0,[z160,z1,z2,z4,z5,z246]),(0,[z0,z1,z64,z2,z4,z129])],[(0,[z0,z1,z2,z4,z5,z282]),(0,[z0,z1,z2,z4,z9,z6]),(0,[z39,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z732,z18]),(0,[z0,z1,z2,z4,z9,z265]),(0,[z280,z0,z2,z4,z9,z6]),(0,[z0,z1,z962,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z465])],[(0,[z0,z1,z2,z4,z963,z6]),(0,[z698,z1,z2,z192,z5,z6]),(0,[z964,z1,z2,z4,z5,z6]),(0,[z0,z47,z29,z4,z5,z162]),(0,[z0,z1,z2,z4,z85,z6]),(0,[z0,z2,z3,z811,z5,z6]),(0,[z0,z1,z33,z4,z16,z6]),(0,[z0,z1,z2,z4,z16,z965])],[(0,[z0,z1,z298,z4,z5,z20]),(0,[z0,z1,z966,z4,z5,z6]),(0,[z0,z1,z967,z2,z4,z5]),(0,[z66,z1,z2,z4,z115,z20]),(0,[z0,z1,z2,z4,z960,z6]),(0,[z0,z1,z2,z4,z968,z6]),(0,[z0,z1,z59,z2,z5,z20])],[(0,[z0,z1,z2,z4,z5,z969]),(0,[z0,z1,z2,z970,z5,z6]),(0,[z165,z1,z155,z4,z9,z6]),(0,[z0,z150,z2,z4,z16,z20]),(0,[z620,z1,z2,z4,z5,z218])]],
   [[(0,[z0,z1,z298,z4,z5,z23]),(0,[z66,z1,z2,z4,z115,z23]),(0,[z1,z2,z4,z5,z732,z6]),(0,[z0,z1,z971,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z972]),(0,[z0,z973,z1,z2,z4,z5]),(0,[z0,z1,z2,z974,z5,z6]),(0,[z111,z1,z2,z4,z174,z6]),(0,[z0,z150,z2,z4,z16,z23]),(0,[z0,z2,z4,z16,z237,z6]),(0,[z0,z1,z2,z4,z975,z6]),(0,[z0,z1,z2,z4,z781,z145])],[(0,[z0,z1,z298,z4,z5,z6]),(0,[z0,z1,z976,z4,z5,z6]),(0,[z66,z1,z2,z4,z115,z6]),(0,[z0,z1,z2,z4,z977,z6]),(0,[z0,z655,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z854,z23])],[(0,[z0,z1,z2,z4,z5,z34]),(0,[z0,z1,z2,z4,z316,z20]),(0,[z0,z1,z328,z4,z5,z289]),(0,[z0,z150,z2,z4,z16,z6])],[(0,[z0,z1,z978,z2,z5,z6]),(0,[z37,z1,z2,z89,z5,z6]),(0,[z0,z1,z2,z4,z5,z979]),(0,[z359,z0,z68,z4,z5,z6]),(0,[z0,z1,z545,z287,z2,z4]),(0,[z1,z155,z729,z4,z5,z6]),(0,[z131,z1,z2,z89,z9,z6]),(0,[z0,z1,z2,z5,z374,z20]),(0,[z0,z1,z2,z4,z16,z205]),(0,[z1,z2,z980,z4,z5,z6])],[(0,[z0,z1,z2,z377,z5,z20]),(0,[z0,z1,z2,z4,z316,z23]),(0,[z0,z47,z29,z4,z16,z6]),(1,[z0,z2,z811,z5,z6]),(0,[z0,z1,z2,z981,z4,z6]),(0,[z0,z188,z2,z4,z9,z24]),(0,[z982,z1,z2,z4,z5,z6]),(0,[z0,z1,z983,z2,z4,z20])],[(0,[z0,z1,z2,z4,z5,z984]),(0,[z0,z1,z985,z2,z4,z5]),(0,[z212,z1,z42,z4,z5,z6]),(0,[z1,z2,z4,z5,z784,z6]),(0,[z0,z1,z328,z4,z5,z99])],[(0,[z0,z1,z2,z4,z316,z6]),(0,[z0,z1,z2,z4,z325,z20]),(0,[z0,z1,z4,z895,z13,z6])]],
   [[(0,[z0,z1,z2,z986,z5,z6]),(0,[z0,z862,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z987]),(0,[z0,z1,z2,z4,z5,z988])],[(0,[z0,z989,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z965]),(0,[z0,z1,z40,z4,z9,z10]),(0,[z0,z1,z2,z4,z325,z23]),(0,[z0,z1,z983,z2,z4,z6]),(0,[z0,z1,z2,z4,z78,z781])],[(0,[z0,z1,z209,z4,z278,z6]),(0,[z0,z2,z4,z990,z5,z6]),(0,[z1,z2,z4,z5,z721,z6]),(0,[z154,z0,z1,z2,z576,z5]),(0,[z0,z1,z40,z2,z576,z5]),(0,[z67,z0,z68,z4,z9,z6]),(0,[z0,z1,z365,z4,z5,z99]),(0,[z0,z1,z2,z16,z991,z6])],[(0,[z0,z1,z2,z4,z5,z992]),(0,[z0,z1,z2,z4,z993,z6]),(0,[z0,z1,z2,z576,z5,z128]),(0,[z0,z1,z328,z4,z16,z6]),(0,[z0,z1,z2,z4,z174,z289]),(0,[z0,z1,z2,z4,z9,z70]),(0,[z0,z1,z2,z518,z5,z23])],[(0,[z148,z1,z42,z4,z9,z6]),(0,[z0,z1,z994,z2,z4,z6]),(0,[z995,z1,z2,z4,z5,z6]),(0,[z0,z252,z2,z811,z5,z6]),(0,[z0,z252,z2,z3,z5,z341]),(0,[z0,z1,z2,z69,z16,z23]),(0,[z0,z1,z614,z4,z5,z344])],[(0,[z0,z1,z2,z4,z238,z282]),(0,[z0,z1,z2,z4,z5,z996]),(0,[z0,z1,z2,z4,z5,z997]),(0,[z998,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z999,z6])],[(0,[z0,z1,z2,z1000,z4,z6]),(0,[z0,z1,z2,z5,z404,z20]),(0,[z1001,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z406,z5,z20]),(0,[z0,z1,z2,z5,z23,z464]),(0,[z0,z1,z2,z4,z5,z1002]),(0,[z0,z1,z2,z407,z5,z20]),(0,[z0,z1,z2,z5,z23,z820])],[(0,[z0,z1,z2,z4,z5,z1003]),(0,[z0,z1,z2,z4,z1004,z6]),(0,[z0,z1,z2,z4,z5,z1005])]],
   [[(0,[z0,z1,z2,z1006,z5,z6]),(0,[z54,z36,z2,z4,z5,z55]),(0,[z0,z1,z2,z1007,z5,z6]),(0,[z0,z1,z2,z4,z530,z20]),(0,[z0,z1,z2,z5,z23,z20])],[(0,[z0,z1,z2,z4,z5,z1008]),(0,[z0,z1,z49,z495,z4,z6]),(0,[z0,z1,z2,z4,z5,z779]),(0,[z0,z1,z2,z5,z23,z472]),(0,[z0,z1,z412,z2,z4,z163])],[(0,[z0,z1,z2,z4,z5,z1009]),(0,[z0,z1,z2,z1010,z5,z6]),(0,[z0,z1,z2,z4,z530,z23])],[(0,[z0,z1,z298,z4,z238,z6]),(0,[z1,z2,z4,z115,z721,z6]),(0,[z0,z1,z2,z4,z1011,z6]),(0,[z0,z97,z29,z4,z5,z6]),(0,[z0,z1,z328,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z1012])],[(0,[z0,z1,z688,z2,z5,z20]),(0,[z0,z1,z2,z4,z5,z1013]),(0,[z0,z1,z2,z4,z530,z6]),(0,[z0,z1,z2,z1014,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1015]),(0,[z0,z1,z328,z4,z5,z23]),(0,[z0,z1,z2,z4,z5,z1016])],[(0,[z54,z36,z2,z51,z5,z6]),(0,[z0,z1,z2,z646,z5,z23]),(1,[z0,z790,z4,z5,z6]),(0,[z0,z1,z2,z4,z1017,z6]),(0,[z1018,z1,z2,z4,z5,z6])],[(0,[z0,z1,z1019,z4,z5,z6]),(0,[z1020,z0,z2,z4,z5,z6]),(0,[z46,z1,z2,z192,z5,z404]),(0,[z0,z1,z365,z4,z5,z20]),(0,[z0,z1,z2,z4,z5,z1021]),(0,[z0,z1,z2,z4,z1022,z23]),(0,[z0,z1,z1023,z4,z5,z23])]],
   [[(0,[z0,z1,z2,z242,z5,z20]),(0,[z0,z1,z1024,z2,z4,z5]),(0,[z17,z1,z2,z4,z9,z18]),(0,[z0,z1,z64,z2,z4,z232]),(0,[z0,z1,z19,z2,z61,z437]),(0,[z63,z1,z2,z4,z5,z200]),(0,[z0,z1,z2,z5,z246,z20])],[(0,[z0,z1,z2,z4,z5,z1025]),(0,[z0,z1,z2,z4,z1026,z6]),(0,[z0,z1,z365,z4,z5,z23]),(0,[z0,z1,z2,z4,z1022,z6]),(0,[z0,z1,z1023,z4,z5,z6])],[(0,[z0,z1,z1027,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1028]),(0,[z0,z1,z2,z4,z1029,z6]),(0,[z0,z1,z4,z5,z895,z6])],[(0,[z0,z1,z365,z4,z5,z6]),(0,[z0,z1,z2,z917,z16,z6]),(0,[z0,z1030,z2,z4,z5,z6])],[(0,[z0,z1,z25,z149,z4,z5]),(0,[z0,z2,z790,z4,z5,z6]),(0,[z0,z1,z328,z4,z174,z6]),(0,[z0,z1,z140,z126,z9,z6]),(0,[z549,z0,z2,z4,z5,z306])],[(0,[z0,z1,z209,z4,z16,z6]),(0,[z0,z1,z2,z4,z5,z1031]),(0,[z533,z1,z155,z4,z5,z6]),(0,[z0,z1,z260,z2,z5,z20]),(0,[z0,z1,z640,z4,z482,z6]),(0,[z0,z1,z12,z4,z895,z6])],[(0,[z0,z188,z1,z2,z576,z5]),(0,[z0,z1,z2,z5,z23,z507]),(0,[z0,z1,z2,z4,z1032,z6]),(0,[z0,z1,z2,z16,z6,z1033]),(0,[z0,z1,z2,z4,z9,z1034]),(0,[z0,z1,z2,z4,z9,z43]),(0,[z1035,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z414,z5,z20])],[(0,[z0,z1,z2,z1036,z5,z6]),(0,[z0,z2,z4,z38,z16,z6]),(0,[z154,z0,z399,z2,z4,z5]),(0,[z0,z1,z1037,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z1038,z5,z6]),(0,[z0,z1,z2,z4,z278,z282]),(0,[z41,z862,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z710]),(0,[z0,z1,z365,z4,z174,z6])],[(0,[z0,z1,z2,z4,z1039,z6]),(0,[z0,z1,z1040,z2,z4,z6]),(0,[z0,z1,z2,z4,z744,z5]),(0,[z0,z1,z2,z4,z16,z81])],[(0,[z0,z1,z2,z4,z5,z1041]),(0,[z0,z1,z243,z2,z89,z20]),(0,[z0,z1,z1042,z4,z5,z6]),(0,[z67,z0,z68,z4,z530,z6]),(0,[z111,z1,z2,z4,z85,z6]),(0,[z0,z417,z2,z4,z16,z6]),(0,[z0,z2,z4,z626,z9,z6]),(0,[z154,z0,z33,z4,z5,z101]),(0,[z0,z1,z2,z168,z5,z20]),(0,[z0,z1,z25,z4,z5,z779]),(0,[z0,z1,z1043,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z307]),(0,[z1,z2,z4,z721,z181,z6]),(0,[z0,z1,z19,z2,z61,z465]),(0,[z0,z2,z4,z5,z880,z20])],[(0,[z0,z1,z2,z4,z5,z1044]),(0,[z0,z47,z790,z4,z5,z6]),(0,[z0,z1,z1045,z2,z4,z6])],[(0,[z54,z36,z2,z546,z5,z6]),(0,[z0,z1,z1046,z2,z4,z6]),(0,[z0,z1,z2,z1047,z5,z6]),(0,[z0,z1,z2,z4,z5,z1048])],[(0,[z0,z1,z298,z4,z278,z6]),(0,[z0,z1,z1049,z4,z5,z6]),(0,[z0,z1,z2,z4,z166,z78])],[(0,[z0,z1,z4,z1050,z5,z6]),(0,[z0,z1,z4,z942,z16,z6]),(0,[z154,z0,z2,z4,z16,z101]),(0,[z0,z1,z2,z124,z125,z20])]],
   [[(0,[z1051,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z1052,z6]),(0,[z0,z1,z2,z4,z1053,z6]),(0,[z0,z1054,z2,z4,z5,z6]),(0,[z66,z1,z2,z4,z317,z6]),(0,[z0,z1,z144,z2,z16,z20]),(0,[z0,z1,z2,z4,z16,z437])],[(0,[z0,z1,z2,z4,z5,z890]),(0,[z131,z1,z2,z1010,z5,z6]),(0,[z0,z1,z2,z4,z5,z1055])],[(0,[z41,z15,z2,z4,z9,z6]),(0,[z1,z2,z1010,z89,z5,z6]),(0,[z0,z1,z2,z4,z5,z224]),(0,[z0,z1,z2,z4,z683,z127])],[(0,[z0,z1,z1056,z2,z4,z6]),(0,[z0,z1,z2,z4,z9,z162]),(0,[z111,z1,z2,z4,z5,z289]),(0,[z39,z1,z2,z4,z5,z289]),(0,[z0,z1,z2,z4,z9,z289])],[(0,[z0,z1,z2,z4,z1057,z6]),(0,[z0,z1,z2,z418,z4,z23]),(0,[z0,z1,z2,z4,z5,z1058]),(0,[z0,z1,z2,z4,z85,z289]),(0,[z0,z1,z4,z5,z20,z1059]),(0,[z0,z1,z2,z4,z6,z781])],[(0,[z0,z1,z2,z4,z5,z732])],[(0,[z0,z1,z2,z4,z1060,z5]),(0,[z0,z1,z2,z4,z9,z99]),(0,[z0,z1,z33,z4,z9,z6]),(0,[z0,z1,z2,z9,z23,z20]),(0,[z0,z1,z40,z4,z5,z623])],[]],
   [[(0,[z0,z1,z248,z326,z2,z4]),(0,[z0,z1,z2,z4,z1061,z6])],[(0,[z0,z1,z1062,z4,z5,z6]),(0,[z54,z36,z2,z4,z5,z20]),(0,[z0,z1,z2,z192,z5,z341]),(0,[z0,z1,z504,z4,z5,z393])],[(0,[z0,z1,z2,z1063,z5,z6]),(0,[z0,z1,z2,z4,z5,z1064]),(0,[z0,z1,z2,z5,z526,z20]),(0,[z0,z1,z40,z4,z5,z779]),(0,[z0,z1,z144,z2,z5,z820]),(0,[z0,z1,z2,z4,z1065,z6])],[(0,[z0,z1,z2,z51,z5,z1003]),(0,[z0,z1,z2,z4,z16,z282]),(0,[z54,z36,z2,z4,z5,z23]),(0,[z39,z1,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z714,z6]),(0,[z0,z1,z2,z4,z16,z465]),(0,[z280,z0,z2,z4,z714,z6]),(0,[z0,z1,z2,z4,z5,z199]),(0,[z0,z175,z2,z4,z5,z171])],[(0,[z0,z1,z2,z4,z1066,z6]),(0,[z66,z1,z120,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z1067]),(0,[z0,z509,z2,z4,z16,z6])],[(0,[z54,z36,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1068,z6]),(0,[z0,z1,z2,z4,z5,z1069]),(0,[z0,z114,z2,z4,z16,z6]),(0,[z46,z1,z2,z192,z5,z142]),(0,[z0,z1,z2,z4,z9,z205]),(0,[z0,z1,z2,z4,z5,z1070])],[(0,[z0,z1,z2,z4,z5,z1071]),(0,[z0,z47,z29,z4,z9,z6]),(0,[z0,z1,z12,z118,z4,z13])],[(0,[z54,z522,z36,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1072])]],
   [[(0,[z0,z1,z2,z4,z5,z1073]),(0,[z0,z1074,z2,z4,z5,z6]),(0,[z0,z1,z2,z1075,z5,z6]),(0,[z0,z1,z245,z2,z4,z232]),(0,[z0,z1,z2,z1076,z5,z6])],[(0,[z0,z1,z298,z4,z16,z6]),(0,[z0,z1077,z2,z4,z5,z6]),(0,[z1,z2,z1010,z4,z5,z6]),(0,[z63,z1,z2,z89,z5,z20])],[(0,[z0,z1,z2,z4,z16,z34]),(0,[z0,z1,z2,z4,z16,z404])],[(0,[z0,z252,z2,z3,z5,z20]),(0,[z280,z0,z2,z4,z9,z20])],[(0,[z0,z1,z2,z1078,z5,z6]),(0,[z111,z1,z328,z4,z5,z6]),(0,[z39,z1,z328,z4,z5,z6]),(0,[z0,z1,z328,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z423])],[(0,[z63,z1,z2,z89,z5,z6]),(0,[z0,z1,z328,z4,z85,z6]),(0,[z280,z0,z2,z4,z9,z23]),(0,[z0,z1,z2,z69,z9,z23]),(0,[z0,z1079,z2,z4,z5,z6]),(0,[z0,z1,z118,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1080]),(0,[z0,z1,z2,z4,z5,z791]),(0,[z0,z1,z2,z4,z20,z1081])],[(0,[z0,z1,z2,z1082,z5,z6]),(0,[z0,z1083,z2,z4,z5,z6]),(0,[z0,z252,z2,z3,z5,z6]),(0,[z0,z1,z2,z4,z9,z894]),(0,[z0,z1,z2,z4,z241,z20]),(0,[z0,z1,z1084,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z1085,z6]),(0,[z0,z1,z2,z134,z5,z20]),(0,[z111,z1,z365,z4,z5,z6])],[(0,[z0,z1,z257,z2,z4,z16]),(0,[z693,z0,z2,z4,z5,z101]),(0,[z0,z1,z365,z4,z85,z6]),(0,[z1086,z1,z2,z4,z5,z6]),(0,[z0,z121,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z1087,z5])],[(0,[z0,z1,z2,z4,z1088,z6]),(0,[z0,z1,z2,z192,z5,z911]),(0,[z0,z1,z2,z124,z28,z6]),(0,[z0,z1,z1089,z2,z4,z20])],[(0,[z0,z1,z287,z2,z4,z16]),(0,[z0,z1,z2,z4,z1090,z6]),(0,[z0,z1,z2,z4,z5,z1091]),(0,[z0,z1,z2,z4,z241,z6]),(0,[z0,z651,z2,z4,z16,z6]),(0,[z0,z1,z305,z4,z135,z6]),(0,[z1092,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1093,z5,z6]),(0,[z0,z1,z2,z4,z1094,z6]),(0,[z39,z1,z2,z4,z174,z6]),(0,[z1095,z1,z2,z4,z5,z6]),(0,[z0,z1,z878,z2,z4,z16]),(0,[z0,z1,z2,z4,z5,z1096]),(0,[z0,z1,z2,z4,z1097,z23])],[(0,[z0,z1,z2,z4,z5,z1098]),(0,[z0,z1,z2,z406,z16,z20])],[(0,[z54,z36,z2,z4,z238,z6]),(0,[z0,z1,z1099,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z404]),(0,[z0,z1,z1089,z2,z4,z6]),(0,[z0,z1,z2,z69,z5,z404]),(0,[z110,z1,z180,z2,z4,z5]),(0,[z0,z1,z2,z4,z16,z1005]),(0,[z0,z1,z2,z4,z225,z94]),(0,[z0,z1,z2,z4,z1097,z6])],[(0,[z329,z1,z2,z4,z5,z18])]],
   [[(0,[z63,z1,z2,z4,z5,z18])],[(0,[z0,z1,z1100,z2,z4,z6]),(0,[z0,z1,z2,z4,z1101,z6]),(0,[z0,z1,z1102,z4,z5,z6]),(0,[z0,z1,z450,z4,z409,z6]),(0,[z0,z1,z12,z4,z135,z6]),(0,[z0,z1,z2,z4,z482,z20]),(0,[z0,z1,z2,z4,z1103,z6])],[(0,[z111,z1,z2,z3,z5,z6]),(0,[z0,z1,z365,z4,z5,z289]),(0,[z0,z1,z912,z2,z4,z5]),(0,[z0,z1,z49,z4,z895,z6])],[(0,[z54,z862,z2,z4,z5,z6]),(0,[z0,z1,z1104,z2,z4,z5]),(0,[z0,z1,z2,z4,z482,z23])],[(0,[z0,z1,z1105,z2,z4,z5]),(0,[z0,z1,z2,z4,z1106,z6]),(0,[z0,z21,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z1107]),(0,[z1108,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z16,z1016]),(0,[z0,z188,z2,z4,z241,z24]),(0,[z0,z1,z2,z4,z1109,z20])],[(0,[z0,z1,z2,z4,z1110,z6]),(0,[z17,z1,z2,z4,z5,z732]),(0,[z0,z1,z2,z4,z5,z1111]),(0,[z0,z1,z2,z4,z482,z6])],[(0,[z0,z1,z209,z4,z9,z6]),(0,[z0,z1,z209,z4,z5,z282]),(0,[z0,z1,z2,z264,z5,z20]),(0,[z0,z1,z2,z4,z5,z1112]),(0,[z0,z362,z2,z4,z16,z6]),(0,[z0,z252,z2,z3,z5,z70]),(0,[z0,z1,z2,z4,z9,z922]),(0,[z0,z1,z2,z4,z65,z127])],[(0,[z0,z1,z287,z29,z4,z5]),(0,[z0,z1,z2,z521,z5,z20]),(0,[z0,z1,z2,z4,z5,z1113]),(0,[z0,z1,z2,z4,z5,z1114]),(0,[z0,z1,z2,z4,z5,z825]),(0,[z58,z0,z2,z4,z5,z101])]],
   [[(0,[z0,z1,z2,z51,z5,z55]),(0,[z0,z1,z1115,z4,z5,z6]),(0,[z123,z1,z2,z4,z721,z6]),(0,[z1116,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1117,z6]),(0,[z0,z1,z2,z4,z1109,z6])],[(0,[z0,z1,z2,z4,z5,z1118]),(0,[z0,z1,z287,z326,z2,z4]),(0,[z0,z1,z2,z521,z5,z23]),(0,[z0,z217,z2,z4,z16,z6])],[(0,[z0,z1,z2,z546,z238,z6]),(0,[z0,z1,z1119,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1120]),(0,[z0,z1,z2,z89,z5,z341]),(0,[z0,z1,z365,z4,z16,z6]),(0,[z0,z2,z4,z714,z5,z6]),(0,[z0,z1,z2,z4,z9,z81]),(0,[z0,z1,z2,z402,z5,z23])],[(0,[z148,z1,z545,z42,z4,z6]),(0,[z0,z1,z2,z521,z5,z6]),(0,[z17,z0,z1,z33,z4,z5]),(0,[z0,z1,z2,z668,z5,z20])],[(0,[z522,z0,z1,z2,z4,z5]),(0,[z0,z1,z1121,z2,z4,z5]),(0,[z0,z229,z2,z4,z16,z6]),(0,[z0,z1,z2,z4,z190,z6]),(0,[z0,z2,z4,z9,z714,z6])],[(0,[z0,z1,z2,z4,z5,z1122]),(0,[z0,z1,z2,z4,z65,z27])],[(0,[z0,z1,z2,z1123,z5,z6]),(0,[z0,z1,z2,z4,z1124,z6]),(0,[z0,z1,z2,z4,z5,z1125]),(0,[z46,z1,z2,z1010,z5,z6]),(0,[z0,z1,z4,z5,z6,z779])],[(0,[z0,z1,z2,z4,z6,z881]),(0,[z123,z1,z230,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z322])]],
   [[(0,[z41,z337,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z16,z142]),(0,[z0,z1,z2,z4,z60,z6]),(0,[z0,z1,z2,z5,z6,z1126]),(0,[z0,z1,z2,z4,z60,z265]),(0,[z0,z1,z1127,z2,z4,z6]),(0,[z154,z0,z2,z4,z9,z101])],[(0,[z54,z36,z2,z4,z278,z6]),(0,[z0,z1,z2,z4,z5,z1128]),(0,[z0,z1,z144,z2,z9,z20]),(0,[z0,z1,z2,z4,z9,z437]),(0,[z0,z1,z2,z4,z5,z1129]),(0,[z0,z1,z4,z5,z6,z1059])],[(0,[z0,z1,z2,z4,z1130,z6]),(0,[z308,z36,z2,z4,z5,z6]),(0,[z148,z1,z326,z42,z4,z6]),(0,[z0,z1,z2,z4,z1131,z6]),(0,[z0,z1,z2,z4,z16,z307]),(0,[z0,z1,z1132,z2,z4,z6])],[(0,[z0,z1,z2,z4,z1133,z6])],[(0,[z0,z1,z2,z4,z5,z1134]),(0,[z0,z1,z2,z4,z5,z1135]),(0,[z0,z2,z4,z9,z309,z6]),(0,[z0,z1,z68,z4,z5,z162]),(0,[z0,z1,z2,z569,z5,z23]),(0,[z0,z1,z140,z126,z5,z423]),(1,[z0,z1,z4,z5,z779])],[(0,[z0,z1,z2,z4,z1136,z6]),(0,[z0,z1,z2,z4,z1137,z6]),(0,[z0,z1,z2,z4,z5,z1138]),(0,[z0,z1,z1139,z2,z4,z6]),(0,[z0,z1,z12,z4,z13,z20]),(0,[z0,z1,z2,z4,z1140,z20])],[(0,[z0,z1,z2,z4,z5,z1141]),(0,[z0,z1,z2,z4,z1142,z6]),(0,[z0,z1,z2,z4,z1143,z6]),(0,[z0,z1,z1144,z2,z4,z5]),(0,[z58,z0,z2,z4,z5,z35])],[(0,[z0,z1,z2,z546,z5,z55]),(0,[z148,z1,z729,z4,z5,z6]),(0,[z0,z1,z19,z2,z515,z6]),(0,[z0,z2,z4,z16,z503,z6]),(0,[z0,z1,z12,z4,z13,z23]),(0,[z0,z1,z4,z5,z1145,z20])]],
   [[(0,[z0,z1,z1146,z4,z5,z6]),(0,[z0,z1,z2,z192,z5,z20]),(0,[z0,z1,z2,z418,z89,z20]),(0,[z110,z1,z2,z4,z16,z128]),(0,[z0,z1,z2,z4,z5,z752]),(0,[z0,z1,z640,z4,z5,z20]),(0,[z0,z2,z4,z5,z101,z725]),(0,[z0,z1,z2,z4,z1147,z6])],[(0,[z46,z1,z2,z192,z5,z20]),(0,[z0,z1,z2,z4,z1148,z6]),(0,[z0,z1,z2,z4,z5,z341]),(0,[z0,z1,z2,z4,z16,z224]),(0,[z0,z1,z12,z4,z13,z6]),(0,[z665,z1,z2,z4,z5,z297]),(0,[z0,z1,z2,z4,z1140,z6])],[(0,[z0,z1,z2,z4,z5,z1149]),(0,[z0,z271,z2,z4,z16,z6]),(0,[z17,z1,z2,z4,z5,z246]),(0,[z378,z0,z68,z4,z5,z6]),(0,[z0,z1,z640,z4,z5,z23])],[(0,[z0,z1,z1043,z4,z5,z23])],[(0,[z0,z1,z2,z4,z9,z282]),(0,[z0,z1,z2,z4,z1150,z6]),(0,[z0,z1,z2,z4,z5,z142]),(0,[z0,z1,z640,z4,z5,z6]),(0,[z111,z1,z2,z4,z9,z6]),(0,[z39,z1,z2,z4,z9,z6]),(0,[z0,z1,z480,z4,z5,z10])],[(0,[z0,z1,z1151,z4,z5,z6]),(0,[z0,z1,z257,z2,z4,z9]),(0,[z0,z1,z248,z2,z4,z16]),(0,[z46,z1,z2,z192,z5,z6]),(0,[z1152,z1,z2,z4,z5,z6]),(0,[z39,z1,z2,z4,z85,z6]),(0,[z0,z1,z2,z321,z5,z20]),(0,[z0,z1,z64,z2,z4,z145])],[(0,[z0,z175,z2,z4,z5,z24])],[(0,[z0,z1,z287,z2,z4,z9]),(0,[z0,z1,z369,z2,z4,z145]),(0,[z154,z0,z2,z4,z325,z101]),(0,[z0,z1,z2,z4,z1153,z6])]],
   [[(0,[z0,z1,z2,z4,z1154,z6]),(0,[z0,z1,z420,z2,z5,z20]),(0,[z110,z1,z2,z4,z5,z732]),(0,[z1155,z1,z2,z4,z5,z6]),(0,[z7,z0,z2,z8,z5,z20])],[(0,[z0,z1,z2,z4,z1156,z6]),(0,[z0,z1,z1157,z4,z5,z6]),(0,[z1,z2,z192,z1010,z5,z6]),(0,[z0,z1,z4,z5,z779,z26]),(0,[z0,z1,z2,z747,z61,z6])],[(0,[z0,z1,z298,z4,z9,z6]),(0,[z0,z1,z298,z4,z5,z282]),(0,[z0,z1,z2,z4,z5,z1158]),(0,[z0,z1,z1159,z2,z4,z6]),(0,[z0,z1,z2,z576,z5,z20]),(0,[z0,z1,z2,z576,z5,z18]),(0,[z0,z1,z953,z2,z4,z16]),(0,[z0,z1,z2,z4,z16,z199])],[(1,[z862,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z34]),(0,[z0,z1,z2,z1160,z5,z6]),(0,[z0,z150,z2,z4,z714,z6]),(0,[z0,z1,z2,z4,z6,z1081]),(0,[z0,z1,z2,z4,z5,z1161]),(0,[z0,z1,z2,z5,z6,z820])],[(0,[z0,z1,z2,z1162,z5,z6]),(0,[z54,z36,z2,z4,z16,z6]),(0,[z110,z1,z2,z4,z5,z128]),(0,[z0,z1,z2,z576,z5,z23]),(0,[z0,z1,z2,z4,z5,z1163]),(0,[z0,z1,z2,z4,z5,z1164]),(0,[z7,z0,z2,z8,z5,z6]),(0,[z0,z1,z2,z4,z5,z1165]),(0,[z0,z1,z2,z358,z5,z23])],[(0,[z0,z1,z2,z4,z5,z1166]),(0,[z0,z303,z2,z4,z16,z6]),(0,[z0,z1,z2,z5,z991,z6]),(0,[z0,z1,z2,z4,z5,z1167])],[(0,[z0,z1,z2,z576,z5,z6]),(0,[z0,z1,z2,z4,z1168,z6]),(0,[z110,z0,z1,z33,z4,z5]),(0,[z1169,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1170])],[(0,[z0,z1,z2,z4,z5,z55]),(0,[z0,z1,z2,z4,z5,z1171]),(0,[z123,z1,z263,z2,z4,z6]),(0,[z17,z1,z2,z521,z5,z18])]],
   [[(0,[z0,z1,z1172,z2,z4,z5]),(0,[z0,z1,z2,z299,z5,z20]),(0,[z0,z1,z2,z4,z5,z1173]),(0,[z0,z1,z179,z2,z5,z20])],[(0,[z0,z1,z2,z51,z5,z20]),(0,[z0,z1,z679,z4,z5,z10]),(0,[z0,z252,z2,z3,z100,z6]),(0,[z0,z1,z2,z4,z166,z291]),(0,[z0,z1,z2,z1174,z5,z6])],[(0,[z0,z600,z29,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z911]),(0,[z0,z1,z2,z4,z1175,z6]),(0,[z0,z1,z412,z2,z4,z145])],[(0,[z0,z1,z2,z4,z1176,z6]),(0,[z0,z1,z2,z4,z5,z801]),(0,[z0,z1,z2,z4,z16,z423]),(0,[z0,z1,z2,z4,z5,z1034])],[(0,[z0,z1,z1177,z2,z4,z6]),(0,[z0,z1,z545,z248,z2,z4]),(0,[z0,z1178,z2,z4,z5,z20])],[(0,[z0,z1,z2,z51,z5,z6]),(0,[z0,z1,z2,z1179,z5,z6]),(0,[z0,z1,z1180,z2,z4,z5]),(0,[z0,z1,z1181,z4,z5,z6]),(1,[z1,z2,z1010,z5,z6]),(0,[z123,z1,z2,z4,z181,z20])],[(0,[z0,z1,z1182,z4,z5,z6]),(0,[z0,z2,z811,z8,z5,z6]),(0,[z0,z252,z2,z3,z16,z6]),(0,[z0,z2,z4,z172,z9,z6]),(0,[z0,z1,z2,z4,z1183,z6])],[(0,[z0,z1,z2,z4,z1184,z6]),(0,[z123,z1,z2,z4,z181,z23]),(0,[z0,z1,z809,z2,z5,z6]),(0,[z0,z1,z140,z126,z5,z322])]],
   [[(0,[z0,z1178,z2,z4,z5,z6]),(0,[z67,z0,z790,z4,z5,z6]),(0,[z0,z1,z2,z4,z76,z20]),(0,[z0,z177,z2,z4,z9,z6])],[(0,[z0,z1,z1185,z4,z5,z6]),(0,[z0,z1,z1186,z2,z4,z6]),(0,[z123,z1,z2,z4,z181,z6]),(0,[z66,z1,z2,z91,z4,z6]),(0,[z0,z1,z2,z4,z1187,z6]),(0,[z0,z1,z25,z4,z5,z157]),(0,[z7,z111,z2,z8,z5,z6]),(0,[z0,z1,z25,z4,z5,z26])],[(0,[z0,z1,z2,z4,z1188,z6]),(0,[z0,z1,z2,z515,z5,z20]),(0,[z123,z1,z2,z4,z684,z6]),(0,[z0,z1,z2,z576,z5,z218]),(0,[z0,z1,z2,z4,z76,z23]),(0,[z0,z1,z2,z519,z5,z20]),(0,[z0,z1189,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z747,z6])],[(0,[z131,z1,z2,z418,z89,z6]),(0,[z0,z1,z2,z4,z5,z1190]),(0,[z0,z1,z2,z4,z5,z913])],[(0,[z0,z1,z2,z4,z76,z6]),(0,[z0,z1,z2,z4,z76,z265]),(0,[z0,z1,z1191,z4,z5,z6]),(0,[z0,z1,z1192,z2,z4,z5]),(0,[z0,z1,z2,z527,z5,z20])],[(0,[z324,z1,z2,z4,z181,z6]),(1,[z0,z1,z2,z4,z781])],[(0,[z0,z1,z2,z4,z5,z1193])],[(0,[z0,z1,z2,z4,z5,z1194]),(0,[z0,z1,z1195,z4,z5,z6]),(0,[z0,z1,z2,z1196,z5,z6]),(0,[z0,z1,z2,z1197,z5,z6]),(0,[z0,z1,z2,z4,z100,z20]),(0,[z0,z1,z33,z4,z482,z6]),(0,[z0,z1,z2,z4,z1198,z20])]],
   [[(0,[z0,z1,z2,z546,z5,z20]),(0,[z0,z1,z2,z4,z238,z55]),(0,[z0,z32,z2,z4,z16,z6]),(0,[z0,z29,z790,z4,z5,z6]),(0,[z0,z252,z2,z3,z5,z23]),(0,[z0,z1,z1199,z2,z4,z5])],[(0,[z0,z1,z2,z89,z5,z20]),(0,[z0,z1,z2,z4,z5,z1200]),(0,[z0,z1,z2,z4,z5,z1201]),(0,[z0,z252,z2,z3,z158,z6]),(0,[z0,z1,z2,z5,z6,z1033])],[(0,[z0,z1,z2,z546,z5,z23]),(0,[z0,z1,z2,z4,z5,z1202]),(0,[z0,z1,z2,z4,z5,z928]),(0,[z0,z1,z2,z4,z5,z1203]),(0,[z0,z1,z4,z5,z6,z1145]),(0,[z1204,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z1028]),(1,[z0,z1,z772,z5,z6])],[(0,[z0,z1205,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z1206,z6]),(0,[z0,z1,z1207,z2,z4,z5]),(0,[z0,z1,z2,z1208,z5,z6]),(0,[z1,z2,z89,z5,z297,z20]),(0,[z39,z1,z365,z4,z5,z6]),(0,[z0,z1,z2,z4,z100,z6]),(0,[z0,z1,z365,z4,z9,z6]),(0,[z1209,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1198,z6]),(0,[z0,z1,z2,z4,z320,z151])],[(0,[z0,z1,z2,z546,z5,z6]),(0,[z0,z1,z624,z4,z578,z6]),(0,[z0,z1,z2,z4,z241,z23])],[(0,[z0,z1,z2,z1210,z5,z6]),(0,[z0,z1,z1211,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1212]),(0,[z0,z1,z2,z240,z5,z20]),(0,[z0,z1,z2,z4,z5,z1213]),(0,[z0,z1,z538,z2,z53,z6]),(0,[z0,z1,z450,z4,z13,z6])],[(0,[z0,z1,z2,z51,z238,z6]),(0,[z111,z1,z2,z8,z5,z6]),(0,[z254,z0,z2,z4,z9,z6])],[(0,[z54,z36,z209,z4,z5,z6]),(0,[z0,z1,z1214,z2,z4,z5]),(0,[z0,z1,z538,z2,z5,z20]),(1,[z0,z1,z4,z895,z6]),(0,[z0,z1,z2,z4,z5,z1215])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 512).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1039).take 300) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1339)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [512, 527, 300] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 99).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 99).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 206).take 50).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [99, 107, 50] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_41166

theorem PEqualNP.Outside.L_meta_41166 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4272483464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4272483464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41166.solve
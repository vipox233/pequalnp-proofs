import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38443

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
  Nat.testBit (4008372928 * 2 ^ 32 + 3938511360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00006d8af02bc42a#64 ++ 0x000036c57815e215#64 ++ 0xde84ff9ff07fc47e#64 ++ 0xef427fcff83fe23f#64 : BitVec 256),
   (0x20391c263698dd98#64 ++ 0x101c8e131b4c6ecc#64 ++ 0x7f7b1c667f99ff99#64 ++ 0xbfbd8e333fccffcc#64 : BitVec 256),
   (0x4782e0585b616ee0#64 ++ 0x23c1702c2db0b770#64 ++ 0x6f83e0787fe1ffe1#64 ++ 0x37c1f03c3ff0fff0#64 : BitVec 256),
   (0x13dc007501d40354#64 ++ 0x09ee003a80ea01aa#64 ++ 0xf7fc007f81fe07ff#64 ++ 0xfbfe003fc0ff03ff#64 : BitVec 256),
   (0x09efb68001ffb000#64 ++ 0x84f7db4000ffd800#64 ++ 0x7bffff8001fff800#64 ++ 0x3dffffc000fffc00#64 : BitVec 256),
   (0x9df7db7fec000000#64 ++ 0x4efbedbff6000000#64 ++ 0x7dfffffffe000000#64 ++ 0x3effffffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0xde84ff9ff07fc47e 0xef427fcff83fe23f

def z1 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x7bffff8001fff800 0x3dffffc000fffc00

def z2 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z3 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x7f7b1c667f99ff99 0xbfbd8e333fccffcc

def z4 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z5 : W := mkw 0x4782eddafb6beeea 0x23c176ed7db5f775 0x6f83fff87fe1ffe1 0x37c1fffc3ff0fff0

def z6 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x7dfffffffe000000 0x3effffffff000000

def z7 : W := mkw 0x00000c023008c408 0x0000060118046204 0x5e001c067019c418 0xaf000e03380ce20c

def z8 : W := mkw 0x20397daef6bbddba 0x101cbed77b5deedd 0xffffffffffffffff 0xffffffffffffffff

def z9 : W := mkw 0x4782e05849612260 0x23c1702c24b09130 0x0080e01800600060 0x0040700c00300030

def z10 : W := mkw 0x67bbfc7e7ff9fff8 0x33ddfe3f3ffcfffc 0x7ffbfc7e7ff9fff9 0xbffdfe3f3ffcfffc

def z11 : W := mkw 0x4200200013616ee0 0x2100100009b0b770 0x6f0300607fe1ffe1 0x378180303ff0fff0

def z12 : W := mkw 0x4782e1d8c9632262 0x23c170ec64b19131 0x8084e39980660066 0x404271ccc0330033

def z13 : W := mkw 0x01c4000000000000 0x00e2000000000000 0x71fc000000000000 0x38fe000000000000

def z14 : W := mkw 0x0823b680002bb000 0x8411db400015d800 0x0803ff800001f800 0x0401ffc00000fc00

def z15 : W := mkw 0x09e7920000000000 0x04f3c90000000000 0x79ffff8000000000 0x3cffffc000000000

def z16 : W := mkw 0x3210087736004fdc 0x1908043b9b0027ee 0x8400007ffe0007ff 0xc200003fff0003ff

def z17 : W := mkw 0x082bb68000bbb000 0x8415db40005dd800 0x7b7bff800199f800 0x3dbdffc000ccfc00

def z18 : W := mkw 0x0039182624900110 0x001c8c1312480088 0x7f7b1c667f980799 0xbfbd8e333fcc03cc

def z19 : W := mkw 0x00006d8ae02b802a 0x000036c57015c015 0x9084ff9f807e007e 0xc8427fcfc03f003f

def z20 : W := mkw 0x20391c2624989118 0x101c8e13124c488c 0x10781c0600180018 0x883c0e03000c000c

def z21 : W := mkw 0x09c6a28001672000 0x84e3514000b39000 0x6b87e38001e7f800 0x35c3f1c000f3fc00

def z22 : W := mkw 0x00006488502bc42a 0x000032442815e215 0xce80e018707fc47e 0xe740700c383fe23f

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0xd684001f807e047e 0xeb42000fc03f023f

def z24 : W := mkw 0x11c4005100000000 0x08e2002880000000 0x0084001980000000 0x0042000cc0000000

def z25 : W := mkw 0xbdf7df7ffe08dc88 0x5efbefbfff046e44 0x7dfffffffe01f800 0x3effffffff00fc00

def z26 : W := mkw 0x0402c00848000000 0x0201600424000000 0x0803e0007e000000 0x0401f0003f000000

def z27 : W := mkw 0x20217d8af62bdcaa 0x1010bec57b15ee55 0x0803ff807e01f800 0x0401ffc03f00fc00

def z28 : W := mkw 0x9df7dfffec0a800a 0x4efbeffff6054005 0xfdfffffffe1e001e 0xfeffffffff0f000f

def z29 : W := mkw 0x1bff927501d43354 0x8dffc93a80ea19aa 0x217b006001803b81 0x10bd803000c01dc0

def z30 : W := mkw 0x1bffb6f501ffb354 0x8dffdb7a80ffd9aa 0xffffffff81ffffff 0xffffffffc0ffffff

def z31 : W := mkw 0x0000000012004c80 0x0000000009002640 0x6f0300607f81ff81 0x378180303fc0ffc0

def z32 : W := mkw 0x20211c023608dc88 0x10108e011b046e44 0x08031c007e01f800 0x04018e003f00fc00

def z33 : W := mkw 0x4feff2585bf57ee0 0xa7f7f92c2dfabf70 0x6ffbe0787fe1ffe1 0x37fdf03c3ff0fff0

def z34 : W := mkw 0x11d4007500000000 0x08ea003a80000000 0x2178006000000000 0x10bc003000000000

def z35 : W := mkw 0x00002480102bc42a 0x000012400815e215 0x82000000007fc47e 0xc1000000003fe23f

def z36 : W := mkw 0x0000490ae0000000 0x0000248570000000 0x5c84ff9ff0000000 0x2e427fcff8000000

def z37 : W := mkw 0x9df792750c000000 0x4efbc93a86000000 0x217b00600e000000 0x10bd803007000000

def z38 : W := mkw 0x95d4497fec000000 0x4aea24bff6000000 0x75fc007ffe000000 0x3afe003fff000000

def z39 : W := mkw 0x09c6a28001672000 0x84e3514000b39000 0x0084e38000660000 0x004271c000330000

def z40 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0xffff1c7fffffffff 0xffff8e3fffffffff

def z41 : W := mkw 0x0000600850214420 0x000030042810a210 0x4e80e0187061c460 0x2740700c3830e230

def z42 : W := mkw 0x4782eddafb6beeea 0x23c176ed7db5f775 0xff87ffffffffffff 0xffc3ffffffffffff

def z43 : W := mkw 0x00000d82a00a800a 0x000006c150054005 0x90041f87801e001e 0xc8020fc3c00f000f

def z44 : W := mkw 0x478280500b402ac0 0x23c1402805a01560 0x210300600f803b81 0x1081803007c01dc0

def z45 : W := mkw 0x0010002400000000 0x0008001200000000 0x7578006600000000 0x3abc003300000000

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x6d0300607e000000 0x368180303f000000

def z47 : W := mkw 0x2008040000989118 0x10040200004c488c 0x0000000000180018 0x80000000000c000c

def z48 : W := mkw 0x47b3f87e7f616ee0 0x23d9fc3f3fb0b770 0x7ffbfc7e7fe1ffe1 0x3ffdfe3f3ff0fff0

def z49 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x297bffe07e000000 0x14bdfff03f000000

def z50 : W := mkw 0x09e7b680002b8000 0x04f3db400015c000 0x7bffff80007fc000 0x3dffffc0003fe000

def z51 : W := mkw 0x13c46ddbf16fc66e 0x09e236edf8b7e337 0xde84ff9ff07fc47e 0xef427fcff83fe23f

def z52 : W := mkw 0x086d1680009e9000 0x84368b40004f4800 0x107c1f80001e0000 0x083e0fc0000f0000

def z53 : W := mkw 0x460040585a004ee0 0x2300202c2d002770 0x040000787e0007e1 0x0200003c3f0003f0

def z54 : W := mkw 0x202914001298dd98 0x10148a00094c6ecc 0x7b7b1c000199ff99 0xbdbd8e0000ccffcc

def z55 : W := mkw 0x13c4005101440244 0x09e2002880a20122 0x8084001980660066 0x4042000cc0330033

def z56 : W := mkw 0x57c6e0595b656ee4 0x2be3702cadb2b772 0xef87e079ffe7ffe7 0x77c3f03cfff3fff3

def z57 : W := mkw 0x29efbe8237fffc88 0x94f7df411bfffe44 0x7bffff807ffff800 0x3dffffc03ffffc00

def z58 : W := mkw 0x0031182624000000 0x00188c1312000000 0x7d7b1c667e000000 0x3ebd8e333f000000

def z59 : W := mkw 0x0000490af000442a 0x0000248578002215 0x8400001ff000047e 0xc200000ff800023f

def z60 : W := mkw 0x09ef920001d43000 0x84f7c90000ea1800 0x217b000001803800 0x10bd800000c01c00

def z61 : W := mkw 0x00000d82a00a800a 0x000006c150054005 0x00001f8000000000 0x00000fc000000000

def z62 : W := mkw 0x00002480002b8000 0x000012400015c000 0x5a84ff80007fc000 0x2d427fc0003fe000

def z63 : W := mkw 0x29ffffaef7fffdba 0x94ffffd77bfffedd 0xffffffffffffffff 0xffffffffffffffff

def z64 : W := mkw 0x8c23db0aec000000 0x4611ed8576000000 0x0803ff807e000000 0x0401ffc03f000000

def z65 : W := mkw 0x9df7fffffc2bc42a 0x4efbfffffe15e215 0xfffffffffe7fc47e 0xffffffffff3fe23f

def z66 : W := mkw 0x4200600853616ee0 0x2100300429b0b770 0x4e80e01871e1ffe1 0x2740700c38f0fff0

def z67 : W := mkw 0x0182a00001612000 0x00c1500000b09000 0x6b83e00001e1f800 0x35c1f00000f0fc00

def z68 : W := mkw 0x21bbbc2637f9fd98 0x10ddde131bfcfecc 0x7ffbfc667ff9ff99 0xbffdfe333ffcffcc

def z69 : W := mkw 0x67bb9c763fd8ffd8 0x33ddce3b1fec7fec 0x7f7b1c667f99ff99 0xbfbd8e333fccffcc

def z70 : W := mkw 0x9431597fec000000 0x4a18acbff6000000 0x7d7b1c7ffe000000 0x3ebd8e3fff000000

def z71 : W := mkw 0x0208000001d40354 0x0104000000ea01aa 0x8200000001fe07ff 0xc100000000ff03ff

def z72 : W := mkw 0x1210007500000354 0x0908003a800001aa 0x8400007f800007ff 0xc200003fc00003ff

def z73 : W := mkw 0x9ff7db7fec000354 0x4ffbedbff60001aa 0xfdfffffffe0007ff 0xfeffffffff0003ff

def z74 : W := mkw 0x0008000000900110 0x0004000000480088 0x0200000001980799 0x8100000000cc03cc

def z75 : W := mkw 0x0befb68001ffb354 0x85f7db4000ffd9aa 0xfbffff8001ffffff 0xfdffffc000ffffff

def z76 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0xff87e07fffffffff 0xffc3f03fffffffff

def z77 : W := mkw 0x6ffffefe7ffffff8 0xb7ffff7f3ffffffc 0x7ffffffe7ffffff9 0xbfffffff3ffffffc

def z78 : W := mkw 0x2010082636004d98 0x100804131b0026cc 0x040000667e000799 0x820000333f0003cc

def z79 : W := mkw 0x9410497fec000000 0x4a0824bff6000000 0x0400007ffe000000 0x0200003fff000000

def z80 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x5c84ff9ff001c000 0x2e427fcff800e000

def z81 : W := mkw 0x01cc000001d40000 0x00e6000000ea0000 0x73fc000001fe0000 0x39fe000000ff0000

def z82 : W := mkw 0x3bffbef737ffffdc 0x9dffdf7b9bffffee 0xffffffffffffffff 0xffffffffffffffff

def z83 : W := mkw 0x4fc6e2d85b676ee0 0xa7e3716c2db3b770 0x6f87e3f87fe7ffe1 0x37c3f1fc3ff3fff0

def z84 : W := mkw 0x105c002500940114 0x082e0012804a008a 0xf77c0067819e079f 0xfbbe0033c0cf03cf

def z85 : W := mkw 0x0582c05848000000 0x02c1602c24000000 0x6d83e0787e000000 0x36c1f03c3f000000

def z86 : W := mkw 0x98751b27a4000000 0x4c3a8d93d2000000 0x107c1f8780000000 0x083e0fc3c0000000

def z87 : W := mkw 0x98755b2fe4000000 0x4c3aad97f2000000 0x5cfcff9ff0000000 0x2e7e7fcff8000000

def z88 : W := mkw 0x4782c0585a004ee0 0x23c1602c2d002770 0x6d83e0787e0007e1 0x36c1f03c3f0003f0

def z89 : W := mkw 0x11d4007500000000 0x08ea003a80000000 0x75fc007f80000000 0x3afe003fc0000000

def z90 : W := mkw 0x9fff92750dd40354 0x4fffc93a86ea01aa 0x217b00600f800381 0x10bd803007c001c0

def z91 : W := mkw 0x9fffdb7fedd40354 0x4fffedbff6ea01aa 0xfffffffffffe07ff 0xffffffffffff03ff

def z92 : W := mkw 0x09e7b20001612000 0x04f3d90000b09000 0x7bffff8001e1f800 0x3dffffc000f0fc00

def z93 : W := mkw 0x13dc6dfff1ffc77e 0x09ee36fff8ffe3bf 0xfffcfffff1ffc7ff 0xfffe7ffff8ffe3ff

def z94 : W := mkw 0x4c23f6885a2bfca0 0xa611fb442d15fe50 0x0803ff807e01f800 0x0401ffc03f00fc00

def z95 : W := mkw 0x13dc497ff1d4477e 0x09ee24bff8ea23bf 0xf7fc007ff1fe07ff 0xfbfe003ff8ff03ff

def z96 : W := mkw 0x20391c2626989998 0x101c8e13134c4ccc 0x317b1c660f983b99 0x98bd8e3307cc1dcc

def z97 : W := mkw 0x4feff6d85bfffee0 0xa7f7fb6c2dffff70 0x7ffffff87fffffe1 0x3ffffffc3ffffff0

def z98 : W := mkw 0x9592c97fec000000 0x4ac964bff6000000 0x6d83e07ffe000000 0x36c1f03fff000000

def z99 : W := mkw 0x4402e0085a216ca0 0x220170042d10b650 0x6f03e0607f81ff81 0x3781f0303fc0ffc0

def z100 : W := mkw 0x460060585b616ee0 0x2300302c2db0b770 0x060000787fe1ffe1 0x0300003c3ff0fff0

def z101 : W := mkw 0x1210497ff000477e 0x090824bff80023bf 0x8400007ff00007ff 0xc200003ff80003ff

def z102 : W := mkw 0x0018002400900110 0x000c001200480088 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z103 : W := mkw 0x0029140000989000 0x00148a00004c4800 0x7b7b1c000199f800 0x3dbd8e0000ccfc00

def z104 : W := mkw 0x33fd1c7737dcdfdc 0x19fe8e3b9bee6fee 0xffff1c7fffffffff 0xffff8e3fffffffff

def z105 : W := mkw 0x9fc6c359c9440244 0x4fe361ace4a20122 0x8084e39980660066 0x404271ccc0330033

def z106 : W := mkw 0x0000490ae0000000 0x0000248570000000 0x0400001ff0000000 0x0200000ff8000000

def z107 : W := mkw 0x440040085a004ca0 0x220020042d002650 0x000000007e000000 0x000000003f000000

def z108 : W := mkw 0x09c6820001442000 0x84e3410000a21000 0x0000000000000000 0x0000000000000000

def z109 : W := mkw 0x2039102406901990 0x101c881203480cc8 0x217b00600f803b81 0x10bd803007c01dc0

def z110 : W := mkw 0x0182a480016ba000 0x00c1524000b5d000 0x7b87ff8001fff800 0x3dc3ffc000fffc00

def z111 : W := mkw 0x0380005001400240 0x01c0002800a00120 0x6780007801e007e1 0x33c0003c00f003f0

def z112 : W := mkw 0x57dee07d5bf56ff4 0x2bef703eadfab7fa 0xffffe07fffffffff 0xfffff03fffffffff

def z113 : W := mkw 0x9dc6c359c8000000 0x4ee361ace4000000 0x0084e39980000000 0x004271ccc0000000

def z114 : W := mkw 0x200804001298dd98 0x10040200094c6ecc 0x6f0300607f99ff99 0xb78180303fccffcc

def z115 : W := mkw 0x01ed140001dc9000 0x00f68a0000ee4800 0x7bff1c0001fff800 0x3dff8e0000fffc00

def z116 : W := mkw 0x31fd1c773698dd98 0x18fe8e3b9b4c6ecc 0x7fff1c7fff99ff99 0xbfff8e3fffccffcc

def z117 : W := mkw 0xd610497ffe004ee0 0x6b0824bfff002770 0x0400007ffe0007e1 0x0200003fff0003f0

def z118 : W := mkw 0xdff7fb7fff616ee0 0x6ffbfdbfffb0b770 0x7fffffffffe1ffe1 0x3ffffffffff0fff0

def z119 : W := mkw 0x4200200013616ee0 0x2100100009b0b770 0x0200000001e1ffe1 0x0100000000f0fff0

def z120 : W := mkw 0x0000490af000442a 0x0000248578002215 0x0000000070000000 0x0000000038000000

def z121 : W := mkw 0x00006188c0230022 0x000030c460118011 0x8084e39980660066 0x404271ccc0330033

def z122 : W := mkw 0x0008248001ffb000 0x8004124000ffd800 0x0200000001fff800 0x0100000000fffc00

def z123 : W := mkw 0xb4395d7ffe98dd98 0x5a1caebfff4c6ecc 0x7f7b1c7fff99ff99 0xbfbd8e3fffccffcc

def z124 : W := mkw 0x20086d8af2bbddba 0x100436c5795deedd 0xde84ff9ff1ffffff 0xef427fcff8ffffff

def z125 : W := mkw 0x00002480102bc42a 0x000012400815e215 0x000000000001c000 0x000000000000e000

def z126 : W := mkw 0x0000000000000000 0x0000000000000000 0x5884ff8000000000 0x2c427fc000000000

def z127 : W := mkw 0x09efff8af1fff42a 0x84f7ffc578fffa15 0xffffff9ff1fffc7e 0xffffffcff8fffe3f

def z128 : W := mkw 0x0000400850004420 0x0000200428002210 0x0400001870000460 0x0200000c38000230

def z129 : W := mkw 0x29ffbea637fffd98 0x94ffdf531bfffecc 0x7fffffe67fffff99 0xbffffff33fffffcc

def z130 : W := mkw 0x9dd6c37dc8000000 0x4eeb61bee4000000 0x75fce3ff80000000 0x3afe71ffc0000000

def z131 : W := mkw 0x105c002500940114 0x082e0012804a008a 0x907c0007801e001e 0xc83e0003c00f000f

def z132 : W := mkw 0x307d1c27249c911c 0x183e8e13924e488e 0x907c1c07801e001e 0xc83e0e03c00f000f

def z133 : W := mkw 0x09ef960000989000 0x04f7cb00004c4800 0x7bffff800199f800 0x3dffffc000ccfc00

def z134 : W := mkw 0x11dc007500900110 0x08ee003a80480088 0x77fc007f81980799 0xbbfe003fc0cc03cc

def z135 : W := mkw 0x09eff788c1ffb022 0x84f7fbc460ffd811 0xfbffff9981fff866 0x7dffffccc0fffc33

def z136 : W := mkw 0x9df7ffffec2bb000 0xcefbfffff615d800 0x7dfffffffe01f800 0x3effffffff00fc00

def z137 : W := mkw 0xbdffdf7ffe98dd98 0x5effefbfff4c6ecc 0x7fffffffff99ff99 0xbfffffffffccffcc

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z139 : W := mkw 0x0000200000210000 0x0000100000108000 0x4a80e0000061c000 0x254070000030e000

def z140 : W := mkw 0x4782e1d8db636ee2 0x23c170ec6db1b771 0xef87e3f9ffe7ffe7 0x77c3f1fcfff3fff3

def z141 : W := mkw 0x11d4007500000000 0x08ea003a80000000 0xf7fc007f807e047e 0xfbfe003fc03f023f

def z142 : W := mkw 0x0180005000000000 0x00c0002800000000 0x6580007800000000 0x32c0003c00000000

def z143 : W := mkw 0x200804001298dd98 0x10040200094c6ecc 0x020000000199ff99 0x8100000000ccffcc

def z144 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x297bff800181f800 0x14bdffc000c0fc00

def z145 : W := mkw 0x9dc6e3d9c8230022 0x4ee371ece4118011 0x8084e39980660066 0x404271ccc0330033

def z146 : W := mkw 0x00080480009e9000 0x80040240004f4800 0x00000000001e0000 0x00000000000f0000

def z147 : W := mkw 0x0208000001d40354 0x0104000000ea01aa 0xd684001f81fe07ff 0xeb42000fc0ff03ff

def z148 : W := mkw 0x187d16a5009e9114 0x8c3e8b52804f488a 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z149 : W := mkw 0x20311c263608dc88 0x10188e131b046e44 0x7d7b1c667e01f800 0x3ebd8e333f00fc00

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0x6b0300000181f800 0x3581800000c0fc00

def z151 : W := mkw 0x9844030180000000 0x4c220180c0000000 0x0004038180000000 0x000201c0c0000000

def z152 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0xa578007f818007ff 0xd2bc003fc0c003ff

def z153 : W := mkw 0x0823ff8af02bf42a 0x8411ffc57815fa15 0x0803ff807001f800 0x0401ffc03800fc00

def z154 : W := mkw 0x00291c023098d408 0x00148e01184c6a04 0x7f7b1c067199fc18 0xbfbd8e0338ccfe0c

def z155 : W := mkw 0x478280501b406ec0 0x23c140280da03760 0x6f0300607f81ff81 0x378180303fc0ffc0

def z156 : W := mkw 0x0400405848000000 0x0200202c24000000 0x040000787e000000 0x0200003c3f000000

def z157 : W := mkw 0x0018002400900110 0x000c001200480088 0x7778006601980799 0xbbbc003300cc03cc

def z158 : W := mkw 0x57deedfffbffeffe 0x2bef76fffdfff7ff 0xffffffffffffffff 0xffffffffffffffff

def z159 : W := mkw 0xdff7db7ffe004ee0 0x6ffbedbfff002770 0x7dfffffffe0007e1 0x3effffffff0003f0

def z160 : W := mkw 0x9dffffffedffb000 0xcefffffff6ffd800 0x7ffffffffffff800 0x3ffffffffffffc00

def z161 : W := mkw 0x4782e4d85b6beee0 0x23c1726c2db5f770 0x7f87fff87fffffe1 0x3fc3fffc3ffffff0

def z162 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0x2178006001800381 0x10bc003000c001c0

def z163 : W := mkw 0x987d1fa7a49e9000 0xcc3e8fd3d24f4800 0x107c1f87801e0000 0x083e0fc3c00f0000

def z164 : W := mkw 0x086fb68000bfb000 0x8437db40005fd800 0x187fff80001ff800 0x0c3fffc0000ffc00

def z165 : W := mkw 0x0008248011fff42a 0x8004124008fffa15 0x8200000001fffc7e 0xc100000000fffe3f

def z166 : W := mkw 0x1bff927501d43354 0x8dffc93a80ea19aa 0xf7ff007f81fe3fff 0xfbff803fc0ff1fff

def z167 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0xfffffffffe7e047e 0xffffffffff3f023f

def z168 : W := mkw 0x678ae4585bf9fff8 0x33c5722c2dfcfffc 0x6f83e0787ff9fff9 0xb7c1f03c3ffcfffc

def z169 : W := mkw 0x20100c263608cd98 0x100806131b0466cc 0x5e001c667e19c799 0xaf000e333f0ce3cc

def z170 : W := mkw 0x13c461d9c1670266 0x09e230ece0b38133 0x8084e39980660066 0x404271ccc0330033

def z171 : W := mkw 0x0000600852214ca0 0x000030042910a650 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z172 : W := mkw 0x19f7927500000000 0x0cfbc93a80000000 0x7dffffff80000000 0x3effffffc0000000

def z173 : W := mkw 0x8c33db2eec000000 0x4619ed9776000000 0x7d7bffe67e000000 0x3ebdfff33f000000

def z174 : W := mkw 0x1200005100000244 0x0900002880000122 0x8000001980000066 0x4000000cc0000033

def z175 : W := mkw 0x09ef920001d40000 0x04f7c90000ea0000 0x7bffff8001fe0000 0x3dffffc000ff0000

def z176 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x10fcff9f80000000 0x087e7fcfc0000000

def z177 : W := mkw 0x09ffbea625ffb000 0x84ffdf5312ffd800 0x7fffffe67ffff800 0x3ffffff33ffffc00

def z178 : W := mkw 0x94004159c8000000 0x4a0020ace4000000 0x0000001980000000 0x0000000cc0000000

def z179 : W := mkw 0xbdffdf7fec989118 0x5effefbff64c488c 0x7dfffffffe180018 0xbeffffffff0c000c

def z180 : W := mkw 0x0000698ae0230022 0x000034c570118011 0xdc84ff9ff0660066 0x6e427fcff8330033

def z181 : W := mkw 0x20391da6a49a911a 0x101c8ed3524d488d 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z182 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x5a84ff80707fc000 0x2d427fc0383fe000

def z183 : W := mkw 0x002914001298dc80 0x00148a00094c6e40 0x7f7b1c607f99ff81 0x3fbd8e303fccffc0

def z184 : W := mkw 0x4208248013fffee0 0xa104124009ffff70 0x0200000001ffffe1 0x0100000000fffff0

def z185 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0x7778006601980799 0xbbbc003300cc03cc

def z186 : W := mkw 0x13c4005101440244 0x09e2002880a20122 0xd684001f807e047e 0xeb42000fc03f023f

def z187 : W := mkw 0x6423fc0a7e29fca8 0x3211fe053f14fe54 0x0803fc007e01f800 0x0401fe003f00fc00

def z188 : W := mkw 0x00004108c0000000 0x0000208460000000 0x0084e39980000000 0x004271ccc0000000

def z189 : W := mkw 0x9fff92750dd40354 0x4fffc93a86ea01aa 0xf7ff007f8ffe07ff 0xfbff803fc7ff03ff

def z190 : W := mkw 0x00006d8af22bccaa 0x000036c57915e655 0xff87ffffffffffff 0xffc3ffffffffffff

def z191 : W := mkw 0x00317daef42bc42a 0x0018bed77a15e215 0xfffffffffe7fc47e 0xffffffffff3fe23f

def z192 : W := mkw 0x125c002501d40354 0x092e001280ea01aa 0x927c000781fe07ff 0xc93e0003c0ff03ff

def z193 : W := mkw 0x8400490aec000000 0x4200248576000000 0x000000007e000000 0x000000003f000000

def z194 : W := mkw 0x0000490ae0000000 0x0000248570000000 0xde84ff9ff07e047e 0xef427fcff83f023f

def z195 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x0800ff807001c000 0x04007fc03800e000

def z196 : W := mkw 0x2008000002901990 0x1004000001480cc8 0x0000000001803b81 0x0000000000c01dc0

def z197 : W := mkw 0x0802a28000232000 0x8401514000119000 0x0000e38000000000 0x000071c000000000

def z198 : W := mkw 0x125c007500940354 0x092e003a804a01aa 0x947c007f801e07ff 0xca3e003fc00f03ff

def z199 : W := mkw 0x4402e0085a216ca0 0x220170042d10b650 0x0803e0007e01f800 0x0401f0003f00fc00

def z200 : W := mkw 0x086d120000941000 0x84368900004a0800 0x0078000000000000 0x003c000000000000

def z201 : W := mkw 0x0029348000bb9000 0x00149a40005dc800 0x7bffff8001fff800 0x3dffffc000fffc00

def z202 : W := mkw 0x0de7d25848000000 0x06f3e92c24000000 0x7dfffff87e000000 0x3efffffc3f000000

def z203 : W := mkw 0x4782e05849612260 0x23c1702c24b09130 0x6d83e0787e600060 0x36c1f03c3f300030

def z204 : W := mkw 0x00004d0af008c42a 0x0000268578046215 0xde001c1ff019c47e 0xef000e0ff80ce23f

def z205 : W := mkw 0x29ffbea625ffb118 0x94ffdf5312ffd88c 0x7bffff8601fff818 0xbdffffc300fffc0c

def z206 : W := mkw 0x0000490ae0000000 0x0000248570000000 0x0800ff8070000000 0x04007fc038000000

def z207 : W := mkw 0x4fefb6d00bffbac0 0xa7f7db6805ffdd60 0x7bffffe00ffffb81 0x3dfffff007fffdc0

def z208 : W := mkw 0xac3bdf2efe98dd98 0x561def977f4c6ecc 0x7f7bffe67f99ff99 0xbfbdfff33fccffcc

def z209 : W := mkw 0x0000000012004c80 0x0000000009002640 0x080300007e01f800 0x040180003f00fc00

def z210 : W := mkw 0x0388005001d40354 0x01c4002800ea01aa 0xe780007801fe07ff 0xf3c0003c00ff03ff

def z211 : W := mkw 0x00002480002b8000 0x000012400015c000 0x0800ff800001c000 0x04007fc00000e000

def z212 : W := mkw 0x2010492ef6004dba 0x100824977b0026dd 0x8400007ffe0007ff 0xc200003fff0003ff

def z213 : W := mkw 0x0208248001ffb354 0x8104124000ffd9aa 0x8200000001ffffff 0xc100000000ffffff

def z214 : W := mkw 0x018aa48001ffb000 0x80c5524000ffd800 0x6b83e00001fff800 0x35c1f00000fffc00

def z215 : W := mkw 0x0000208000230022 0x0000104000118011 0x8000000000660066 0x4000000000330033

def z216 : W := mkw 0x4fc6e2d849672260 0xa7e3716c24b39130 0x0084e39800660060 0x004271cc00330030

def z217 : W := mkw 0xbfffdf7fffdcdfdc 0x5fffefbfffee6fee 0xffffffffffffffff 0xffffffffffffffff

def z218 : W := mkw 0x0008000000940114 0x00040000004a008a 0x80000000001e001e 0xc0000000000f000f

def z219 : W := mkw 0x09ef968001deb000 0x84f7cb4000ef5800 0x317f1f80019e3800 0x18bf8fc000cf1c00

def z220 : W := mkw 0x0029140000989000 0x00148a00004c4800 0x10781c0000180000 0x083c0e00000c0000

def z221 : W := mkw 0x0380005013404ec0 0x01c0002809a02760 0x6f8300787fe1ffe1 0x37c1803c3ff0fff0

def z222 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0xffffff9f81fffc7e 0xffffffcfc0fffe3f

def z223 : W := mkw 0x20391c263498d518 0x101c8e131a4c6a8c 0x5e781c067019c418 0xaf3c0e03380ce20c

def z224 : W := mkw 0x13cc005101d40354 0x09e6002880ea01aa 0x8284001981fe07ff 0xc142000cc0ff03ff

def z225 : W := mkw 0x5792e07d5b616ff4 0x2bc9703eadb0b7fa 0xef83e07fffe1ffff 0xf7c1f03ffff0ffff

def z226 : W := mkw 0x1010002500000114 0x080800128000008a 0x800000078000001e 0xc0000003c000000f

def z227 : W := mkw 0x0000698af023442a 0x000034c57811a215 0x8484e39ff066047e 0xc24271cff833023f

def z228 : W := mkw 0xb87d1f27b698dd98 0x5c3e8f93db4c6ecc 0x7f7f1fe7ff99ff99 0xbfbf8ff3ffccffcc

def z229 : W := mkw 0x0000000000000000 0x0000000000000000 0x90040007801e001e 0xc8020003c00f000f

def z230 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0xa378006001fe07ff 0xd1bc003000ff03ff

def z231 : W := mkw 0x4782e05849612260 0x23c1702c24b09130 0x6b83e01801e1f860 0x35c1f00c00f0fc30

def z232 : W := mkw 0x1044000100040004 0x0822000080020002 0x8004000180060006 0x40020000c0030003

def z233 : W := mkw 0x0000000002000880 0x0000000001000440 0x210300600f803b81 0x1081803007c01dc0

def z234 : W := mkw 0x29ffb6a407ffb990 0x94ffdb5203ffdcc8 0x7bffffe00ffffb81 0x3dfffff007fffdc0

def z235 : W := mkw 0x0befb6d001ffb240 0x85f7db6800ffd920 0x7ffffff801ffffe1 0x3ffffffc00fffff0

def z236 : W := mkw 0x1bfffffff1fff77e 0x8dfffffff8fffbbf 0xfffffffff1ffffff 0xfffffffff8ffffff

def z237 : W := mkw 0x4782a0500b612ac0 0x23c1502805b09560 0x6b83e0600fe1fb81 0x35c1f03007f0fdc0

def z238 : W := mkw 0x00006c0a7029c428 0x000036053814e214 0x5e80fc1e7079c478 0xaf407e0f383ce23c

def z239 : W := mkw 0x0008000001d43000 0x8004000000ea1800 0x0000000001803800 0x0000000000c01c00

def z240 : W := mkw 0x1bffb6f501ffb354 0x8dffdb7a80ffd9aa 0x7bffffe001fffb81 0x3dfffff000fffdc0

def z241 : W := mkw 0x2008248012bbddba 0x10041240095deedd 0x8200000001ffffff 0xc100000000ffffff

def z242 : W := mkw 0x13cc005101d40244 0x09e6002880ea0122 0xf3fc001981fe0066 0x79fe000cc0ff0033

def z243 : W := mkw 0x4200000012004ee0 0x2100000009002770 0x00000000000007e1 0x00000000000003f0

def z244 : W := mkw 0x13d4007500000354 0x09ea003a800001aa 0xf5fc007f800007ff 0xfafe003fc00003ff

def z245 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x0883e0187e61f860 0x0441f00c3f30fc30

def z246 : W := mkw 0x478ae0585bf56ff4 0x23c5702c2dfab7fa 0xef83e0787fffffff 0xf7c1f03c3fffffff

def z247 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x0280e01801e1ffe1 0x0140700c00f0fff0

def z248 : W := mkw 0x9deff7d9c9ffb000 0xcef7fbece4ffd800 0x7bffff9981fff800 0x3dffffccc0fffc00

def z249 : W := mkw 0x0380005001400240 0x01c0002800a00120 0xf784007f81fe07ff 0xfbc2003fc0ff03ff

def z250 : W := mkw 0x9dffdfffec9e9000 0xceffeffff64f4800 0x7dfffffffe1e0000 0x3effffffff0f0000

def z251 : W := mkw 0x33fd1c7725dc935c 0x19fe8e3b92ee49ae 0xf7fc1c7f81fe07ff 0xfbfe0e3fc0ff03ff

def z252 : W := mkw 0x57dee07d49f52374 0x2bef703ea4fa91ba 0xf7fce07f81fe07ff 0xfbfe703fc0ff03ff

def z253 : W := mkw 0x20291c023698dc88 0x10148e011b4c6e44 0x7b7b1c007f99f800 0x3dbd8e003fccfc00

def z254 : W := mkw 0x09c6ef8af16fe42a 0x84e377c578b7f215 0xde84ff9ff07fc47e 0xef427fcff83fe23f

def z255 : W := mkw 0xbdf7db7ffe004d98 0x5efbedbfff0026cc 0x7dfffffffe000799 0xbeffffffff0003cc

def z256 : W := mkw 0x0000600850214420 0x000030042810a210 0x0800e0007001c000 0x040070003800e000

def z257 : W := mkw 0x8c02c308c8000000 0x4601618464000000 0x0000e38000000000 0x000071c000000000

def z258 : W := mkw 0x57c6e05949652264 0x2be3702ca4b29132 0x8084e01980660066 0x4042700cc0330033

def z259 : W := mkw 0x33fd1c7737dcdfdc 0x19fe8e3b9bee6fee 0x7f7b1c667f99ff99 0xbfbd8e333fccffcc

def z260 : W := mkw 0x01c4000001440000 0x00e2000000a20000 0x0084000000660000 0x0042000000330000

def z261 : W := mkw 0x0182a00013616c80 0x00c1500009b0b640 0x6f83e0607fe1ff81 0x37c1f0303ff0ffc0

def z262 : W := mkw 0x99f51b77a4000000 0x4cfa8dbbd2000000 0x75fc1fff80000000 0x3afe0fffc0000000

def z263 : W := mkw 0x082bb68001ffb000 0x8415db4000ffd800 0x0a03ff8001fff800 0x0501ffc000fffc00

def z264 : W := mkw 0x0782c05849400240 0x03c1602c24a00120 0x6f83e0787fe007e1 0x37c1f03c3ff003f0

def z265 : W := mkw 0x8defff8aedffb000 0xc6f7ffc576ffd800 0x7bffff807ffff800 0x3dffffc03ffffc00

def z266 : W := mkw 0x13dc007513d44fd4 0x09ee003a89ea27ea 0xffff007fffffffff 0xffff803fffffffff

def z267 : W := mkw 0x0000080220000000 0x0000040110000000 0x5c001c0670000000 0x2e000e0338000000

def z268 : W := mkw 0x20393ca636bbddba 0x101c9e531b5deedd 0xff7b1c667fffffff 0xffbd8e333fffffff

def z269 : W := mkw 0x0031592ee4000000 0x0018ac9772000000 0x7dfffffffe000000 0x3effffffff000000

def z270 : W := mkw 0x20391da6b69add9a 0x101c8ed35b4d6ecd 0xff7f1fe7ff9fff9f 0xffbf8ff3ffcfffcf

def z271 : W := mkw 0x98751fa7a40a800a 0x4c3a8fd3d2054005 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z272 : W := mkw 0x2208040013dcdfdc 0x1104020009ee6fee 0x8200000001ffffff 0xc100000000ffffff

def z273 : W := mkw 0x086d368001ffb000 0x84369b4000ffd800 0x127c1f8001fff800 0x093e0fc000fffc00

def z274 : W := mkw 0x17dec07d49d40354 0x0bef603ea4ea01aa 0xffffe07ffffe07ff 0xfffff03fffff03ff

def z275 : W := mkw 0x0000690af021442a 0x000034857810a215 0xce80e01ff061c47e 0xe740700ff830e23f

def z276 : W := mkw 0x09c6820000000000 0x04e3410000000000 0x0084e38000000000 0x004271c000000000

def z277 : W := mkw 0x9de7d359c8000000 0x4ef3e9ace4000000 0x79ffff9980000000 0x3cffffccc0000000

def z278 : W := mkw 0xb410497ffe004d98 0x5a0824bfff0026cc 0x0400007ffe000799 0x8200003fff0003cc

def z279 : W := mkw 0x00000c023008c408 0x0000060118046204 0xde841c1ff07fc47e 0xef420e0ff83fe23f

def z280 : W := mkw 0x19ffb6a501ffb114 0x8cffdb5280ffd88a 0xfbffff8781fff81e 0xfdffffc3c0fffc0f

def z281 : W := mkw 0xb87d1f27a4989118 0x5c3e8f93d24c488c 0x107c1f8780180018 0x883e0fc3c00c000c

def z282 : W := mkw 0xdfc6e359c9612260 0x6fe371ace4b09130 0x0084e39980600060 0x004271ccc0300030

def z283 : W := mkw 0x9df7db7ffc00442a 0x4efbedbffe002215 0xfdfffffffe00047e 0xfeffffffff00023f

def z284 : W := mkw 0x00000c023208cc88 0x0000060119046644 0x7f031c667f99ff99 0xbf818e333fccffcc

def z285 : W := mkw 0x20393ca637fffd98 0x901c9e531bfffecc 0x7f7b1c667fffff99 0xbfbd8e333fffffcc

def z286 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x9804ff87f01fc01e 0xcc027fc3f80fe00f

def z287 : W := mkw 0x4380205013616ee0 0x21c0102809b0b770 0x6780007801e1ffe1 0x33c0003c00f0fff0

def z288 : W := mkw 0x11f5187724000000 0x08fa8c3b92000000 0x7dff1c7ffe000000 0x3eff8e3fff000000

def z289 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x297b1c607f81fb81 0x14bd8e303fc0fdc0

def z290 : W := mkw 0x09ffb6a401ffb110 0x84ffdb5200ffd888 0x7fffffe601ffff99 0xbffffff300ffffcc

def z291 : W := mkw 0x0582805008000000 0x02c1402804000000 0x210300600e000000 0x1081803007000000

def z292 : W := mkw 0x9fffffffedffb354 0xcffffffff6ffd9aa 0xffffffffffffffff 0xffffffffffffffff

def z293 : W := mkw 0x8de7db0aec000000 0x46f3ed8576000000 0x79ffff807e000000 0x3cffffc03f000000

def z294 : W := mkw 0x440280000a002880 0x2201400005001440 0x000300000e003800 0x0001800007001c00

def z295 : W := mkw 0x20397c2e76b9ddb8 0x101cbe173b5ceedc 0x7ffbfc7e7ff9fff9 0xbffdfe3f3ffcfffc

def z296 : W := mkw 0xac23df0afe08dc88 0x5611ef857f046e44 0x0803ff807e01f800 0x0401ffc03f00fc00

def z297 : W := mkw 0x00002480002b8000 0x000012400015c000 0xde84ff9f807fc47e 0xef427fcfc03fe23f

def z298 : W := mkw 0x2018082636904d98 0x100c04131b4826cc 0x777800667f980799 0xbbbc00333fcc03cc

def z299 : W := mkw 0x08211680000a9000 0x84108b4000054800 0x00001f8000000000 0x00000fc000000000

def z300 : W := mkw 0x11dc002501d40114 0x08ee001280ea008a 0xf3fc000781fe001e 0xf9fe0003c0ff000f

def z301 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x10fcff80007e0000 0x087e7fc0003f0000

def z302 : W := mkw 0x200004001208dc88 0x1000020009046e44 0x000000000001f800 0x000000000000fc00

def z303 : W := mkw 0x09e7b680002bb000 0x84f3db400015d800 0x79ffff800001f800 0x3cffffc00000fc00

def z304 : W := mkw 0x00004108c0000022 0x0000208460000011 0x8000001980000066 0x4000000cc0000033

def z305 : W := mkw 0x11dc007500940114 0x08ee003a804a008a 0xf5fc007f801e001e 0xfafe003fc00f000f

def z306 : W := mkw 0xdff7ffffff6beeea 0x6ffbffffffb5f775 0xffffffffffffffff 0xffffffffffffffff

def z307 : W := mkw 0x9875122504000000 0x4c3a891282000000 0x0078000000000000 0x003c000000000000

def z308 : W := mkw 0x0582e05858214420 0x02c1702c2c10a210 0x6f83e0787e61c460 0x37c1f03c3f30e230

def z309 : W := mkw 0x4fe7f2585b616ee0 0x27f3f92c2db0b770 0x7ffffff87fe1ffe1 0x3ffffffc3ff0fff0

def z310 : W := mkw 0x105c0da7a09e811e 0x082e06d3d04f408f 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z311 : W := mkw 0x4600495afa004eea 0x230024ad7d002775 0x8400007ffe0007ff 0xc200003fff0003ff

def z312 : W := mkw 0x0000080230004408 0x0000040118002204 0x0400000670000418 0x820000033800020c

def z313 : W := mkw 0x9410497fec000000 0x4a0824bff6000000 0x5c84fffffe000000 0x2e427fffff000000

def z314 : W := mkw 0x20397daef4bbd53a 0x101cbed77a5dea9d 0xdefcff9ff07fc47e 0xef7e7fcff83fe23f

def z315 : W := mkw 0x086d1f82a09e900a 0x84368fc1504f4805 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z316 : W := mkw 0x941000750c000000 0x4a08003a86000000 0x000000600e000000 0x0000003007000000

def z317 : W := mkw 0x13c4005101440244 0x09e2002880a20122 0x0000000000000000 0x0000000000000000

def z318 : W := mkw 0x33fd107507d41bd4 0x19fe883a83ea0dea 0xf7ff007f8ffe3fff 0xfbff803fc7ff1fff

def z319 : W := mkw 0x09eff68851fff420 0x84f7fb4428fffa10 0x7fffff9871fffc60 0x3fffffcc38fffe30

def z320 : W := mkw 0x0021180224000000 0x00108c0112000000 0x08031c007e000000 0x04018e003f000000

def z321 : W := mkw 0x09efb68013fffc80 0x84f7db4009fffe40 0x7fffffe07fffff81 0x3ffffff03fffffc0

def z322 : W := mkw 0x01abb40001f9b000 0x00d5da0000fcd800 0x7bfbfc0001f9f800 0x3dfdfe0000fcfc00

def z323 : W := mkw 0x4782e0584b612ae0 0x23c1702c25b09570 0x2183e0780fe03be1 0x10c1f03c07f01df0

def z324 : W := mkw 0x00311c263408c408 0x00188e131a046204 0x7f7b1c667e19c418 0xbfbd8e333f0ce20c

def z325 : W := mkw 0x4782e05859616660 0x23c1702c2cb0b330 0x4e80e0187061c460 0x2740700c3830e230

def z326 : W := mkw 0x03cc000001d40354 0x01e6000000ea01aa 0xf3fc000001fe07ff 0xf9fe000000ff03ff

def z327 : W := mkw 0x9df79a772c000000 0x4efbcd3b96000000 0x7d7b1c667e000000 0x3ebd8e333f000000

def z328 : W := mkw 0x9dffdf7fec989000 0x4effefbff64c4800 0x7fffffffff99f800 0x3fffffffffccfc00

def z329 : W := mkw 0x00000d82b00ac40a 0x000006c158056205 0xde041f87f01fc41e 0xef020fc3f80fe20f

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0x52840000007e0000 0x29420000003f0000

def z331 : W := mkw 0x086d7f8af0bfd42a 0x8436bfc5785fea15 0xdefcff9ff07fc47e 0xef7e7fcff83fe23f

def z332 : W := mkw 0x67bb90740fd03bd0 0x33ddc83a07e81de8 0x217b00600f803b81 0x10bd803007c01dc0

def z333 : W := mkw 0x9dc6c359c8000000 0x4ee361ace4000000 0x6d87e3f9fe000000 0x36c3f1fcff000000

def z334 : W := mkw 0x0218002401d40354 0x010c001200ea01aa 0xf778006601fe07ff 0xfbbc003300ff03ff

def z335 : W := mkw 0x9410497ffc00442a 0x4a0824bffe002215 0x8400007ffe00047e 0xc200003fff00023f

def z336 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x14781c667e180799 0x8a3c0e333f0c03cc

def z337 : W := mkw 0x4200200001612260 0x2100100000b09130 0x0000000000600060 0x0000000000300030

def z338 : W := mkw 0x29ff9e263698dd98 0x14ffcf131b4c6ecc 0x7fffffe67f99ff99 0xbffffff33fccffcc

def z339 : W := mkw 0x1befb6d101ffb244 0x8df7db6880ffd922 0xfbffff9981fff866 0x7dffffccc0fffc33

def z340 : W := mkw 0x2039102406901990 0x101c881203480cc8 0x777b00660f983f99 0xbbbd803307cc1fcc

def z341 : W := mkw 0x09f79a2624000000 0x04fbcd1312000000 0x7dffffe67e000000 0x3efffff33f000000

def z342 : W := mkw 0x97dc497fedd40354 0x4bee24bff6ea01aa 0xf7fc007ffffe07ff 0xfbfe003fffff03ff

def z343 : W := mkw 0x105c6daff0bfc53e 0x082e36d7f85fe29f 0xdefcff9ff07fc47e 0xef7e7fcff83fe23f

def z344 : W := mkw 0x20211c0224089008 0x10108e0112044804 0x00001c0000000000 0x00000e0000000000

def z345 : W := mkw 0x09a3b680016bb000 0x84d1db4000b5d800 0x6b83ff8001e1f800 0x35c1ffc000f0fc00

def z346 : W := mkw 0x8c23db0aec000000 0x4611ed8576000000 0x5c87ff9ffe000000 0x2e43ffcfff000000

def z347 : W := mkw 0x13dea07501f52354 0x09ef503a80fa91aa 0xffffe07f81ffffff 0xfffff03fc0ffffff

def z348 : W := mkw 0x00006188c0230022 0x000030c460118011 0xd684e39f807e047e 0xeb4271cfc03f023f

def z349 : W := mkw 0x0000000010004400 0x0000000008002200 0x4e0000007001c400 0x270000003800e200

def z350 : W := mkw 0x57de80750bd42bd4 0x2bef403a85ea15ea 0xf7ff007f8ffe3fff 0xfbff803fc7ff1fff

def z351 : W := mkw 0x8c23ff8afc2bc42a 0x4611ffc57e15e215 0x0803ff807e01c000 0x0401ffc03f00e000

def z352 : W := mkw 0x0deff6d849ffb000 0x86f7fb6c24ffd800 0x7ffffff87ffff800 0x3ffffffc3ffffc00

def z353 : W := mkw 0x98757faff42bc42a 0x4c3abfd7fa15e215 0xdefcff9ff07fc47e 0xef7e7fcff83fe23f

def z354 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0x67f8007801e007e1 0x33fc003c00f003f0

def z355 : W := mkw 0x0031182636004c80 0x00188c131b002640 0x7f7b1c667f81ff81 0x3fbd8e333fc0ffc0

def z356 : W := mkw 0x0039142400989110 0x001c8a12004c4888 0x7f7b1c660199ff99 0xbfbd8e3300ccffcc

def z357 : W := mkw 0x4fa3f6d85b6bfee0 0xa7d1fb6c2db5ff70 0x6f83fff87fe1ffe1 0x37c1fffc3ff0fff0

def z358 : W := mkw 0x1010007500000000 0x0808003a80000000 0x0400007f80000000 0x0200003fc0000000

def z359 : W := mkw 0x0018002400900110 0x000c001200480088 0x1078000600180018 0x883c0003000c000c

def z360 : W := mkw 0x22391c2637dcdfdc 0x111c8e131bee6fee 0xff7b1c667fffffff 0xffbd8e333fffffff

def z361 : W := mkw 0xdff7db7fef402ac0 0x6ffbedbff7a01560 0x7dffffffff803b81 0x3effffffffc01dc0

def z362 : W := mkw 0x00006d8ae02b8000 0x000036c57015c000 0x5e84ff9ff07fc000 0x2f427fcff83fe000

def z363 : W := mkw 0x0823920000003000 0x8411c90000001800 0x0003000000003800 0x0001800000001c00

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0x8084001980660066 0x4042000cc0330033

def z365 : W := mkw 0x2039102416905d90 0x101c88120b482ec8 0x6f7b00607f81ff81 0x37bd80303fc0ffc0

def z366 : W := mkw 0x00086d8af1fff42a 0x800436c578fffa15 0xde84ff9ff1fffc7e 0xef427fcff8fffe3f

def z367 : W := mkw 0x13d4007501400240 0x09ea003a80a00120 0x77fc007f81e007e1 0x3bfe003fc0f003f0

def z368 : W := mkw 0xd792e97fff616ee0 0x6bc974bfffb0b770 0x6f83e07fffe1ffe1 0x37c1f03ffff0fff0

def z369 : W := mkw 0x88211b02a4000000 0x44108d8152000000 0x00001f8000000000 0x00000fc000000000

def z370 : W := mkw 0x0000000000000000 0x0000000000000000 0x6700006001800781 0x3380003000c003c0

def z371 : W := mkw 0x00006188d0234422 0x000030c46811a211 0xce84e399f067c466 0x674271ccf833e233

def z372 : W := mkw 0x33dc087737d44fdc 0x19ee043b9bea27ee 0xf7fc007ffffe07ff 0xfbfe003fffff03ff

def z373 : W := mkw 0x47abf4585bf9fee0 0x23d5fa2c2dfcff70 0x7ffbfc787ff9ffe1 0x3ffdfe3c3ffcfff0

def z374 : W := mkw 0x287d1ea6249e9118 0x943e8f53124f488c 0x107c1f86001e0018 0x883e0fc3000f000c

def z375 : W := mkw 0x13dc61fdc1f70376 0x09ee30fee0fb81bb 0xf7fce3ff81fe07ff 0xfbfe71ffc0ff03ff

def z376 : W := mkw 0x1bdea2f501f72354 0x8def517a80fb91aa 0xf7fce3ff81fe07ff 0xfbfe71ffc0ff03ff

def z377 : W := mkw 0x00006488502bc420 0x000032442815e210 0x5e84ff98707fc460 0x2f427fcc383fe230

def z378 : W := mkw 0x0200000001440244 0x0100000000a20122 0x8000000000660066 0x4000000000330033

def z379 : W := mkw 0x9c77db2fec000000 0x4e3bed97f6000000 0x187fff87fe000000 0x0c3fffc3ff000000

def z380 : W := mkw 0x09efb68011fff42a 0x84f7db4008fffa15 0xfbffff8001fffc7e 0xfdffffc000fffe3f

def z381 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0x90fc001f807e007e 0xc87e000fc03f003f

def z382 : W := mkw 0x2031182636004d98 0x10188c131b0026cc 0x7d7b1c667e000799 0xbebd8e333f0003cc

def z383 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x187b1c067e19f818 0x8c3d8e033f0cfc0c

def z384 : W := mkw 0x5610407d5a004ff4 0x2b08203ead0027fa 0x8400007ffe0007ff 0xc200003fff0003ff

def z385 : W := mkw 0x0582c0585a004c80 0x02c1602c2d002640 0x6f83e0787f81ff81 0x37c1f03c3fc0ffc0

def z386 : W := mkw 0x0000690af0214420 0x000034857810a210 0x5e84ff9ff061c460 0x2f427fcff830e230

def z387 : W := mkw 0x20180c263698dd98 0x100c06131b4c6ecc 0x060000667f99ff99 0x830000333fccffcc

def z388 : W := mkw 0x01cc000001d40000 0x00e6000000ea0000 0x2178000001800000 0x10bc000000c00000

def z389 : W := mkw 0x9dfffffffdfff42a 0xcefffffffefffa15 0xfffffffffffffc7e 0xfffffffffffffe3f

def z390 : W := mkw 0x33fd107507d41bd4 0x19fe883a83ea0dea 0x217b00600f803b81 0x10bd803007c01dc0

def z391 : W := mkw 0x4782e05849612260 0x23c1702c24b09130 0x6780e07801e007e1 0x33c0703c00f003f0

def z392 : W := mkw 0x00002480002b8000 0x000012400015c000 0x02000000007fc000 0x01000000003fe000

def z393 : W := mkw 0x66395c7e7e98dff8 0x331cae3f3f4c6ffc 0x7f7b1c7e7f99fff9 0xbfbd8e3f3fccfffc

def z394 : W := mkw 0x4402ed8afa2becaa 0x220176c57d15f655 0xde87ff9ffe7ffc7e 0xef43ffcfff3ffe3f

def z395 : W := mkw 0x460040585a004ee0 0x2300202c2d002770 0x6f0300787f81ffe1 0x3781803c3fc0fff0

def z396 : W := mkw 0x9dc6cb5be8000000 0x4ee365adf4000000 0x5c84ff9ff0000000 0x2e427fcff8000000

def z397 : W := mkw 0x0000400840000000 0x0000200420000000 0x4c80e01870000000 0x2640700c38000000

def z398 : W := mkw 0xffffff7ffff9fff8 0x7fffffbffffcfffc 0x7ffffffffff9fff9 0xbffffffffffcfffc

def z399 : W := mkw 0x0582e05849612000 0x02c1702c24b09000 0x6f83e0787fe1f800 0x37c1f03c3ff0fc00

def z400 : W := mkw 0x643bfc2e7eb9fdb8 0x321dfe173f5cfedc 0x7f7bfc667f99ff99 0xbfbdfe333fccffcc

def z401 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x0480e0787e6007e1 0x0240703c3f3003f0

def z402 : W := mkw 0x01cc248001ffb000 0x80e6124000ffd800 0x73fc000001fff800 0x39fe000000fffc00

def z403 : W := mkw 0x13fd187725d40354 0x09fe8c3b92ea01aa 0xffff1c7ffffe07ff 0xffff8e3fffff03ff

def z404 : W := mkw 0x0582eddaf82bc42a 0x02c176ed7c15e215 0xff87fffffe7fc47e 0xffc3ffffff3fe23f

def z405 : W := mkw 0x33dc047513dcdfdc 0x19ee023a89ee6fee 0xf7fc007f81ffffff 0xfbfe003fc0ffffff

def z406 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x257b007ffe000000 0x12bd803fff000000

def z407 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x8884ff99f067c066 0x44427fccf833e033

def z408 : W := mkw 0x67bbf07c5ff17ff0 0x33ddf83e2ff8bff8 0x6ffbe0787fe1ffe1 0x37fdf03c3ff0fff0

def z409 : W := mkw 0x4782c0584b402ac0 0x23c1602c25a01560 0x6d83e0787f803b81 0x36c1f03c3fc01dc0

def z410 : W := mkw 0x9c755b7fec000000 0x4e3aadbff6000000 0x147c1ffffe000000 0x0a3e0fffff000000

def z411 : W := mkw 0x09c6a680016fa000 0x84e3534000b7d000 0x5a84ff80007fc000 0x2d427fc0003fe000

def z412 : W := mkw 0x0000200010214420 0x000010000810a210 0x020000000061c460 0x010000000030e230

def z413 : W := mkw 0x4deff6885bfffca0 0xa6f7fb442dfffe50 0x7bffff807ffff800 0x3dffffc03ffffc00

def z414 : W := mkw 0x0000000012004c80 0x0000000009002640 0x040000607e000781 0x020000303f0003c0

def z415 : W := mkw 0x0008000000900000 0x0004000000480000 0x7378000001980000 0x39bc000000cc0000

def z416 : W := mkw 0x11dc007501d40000 0x08ee003a80ea0000 0x77fc007f81fe0000 0x3bfe003fc0ff0000

def z417 : W := mkw 0x9ff7db7fed400240 0x4ffbedbff6a00120 0x7fffffffffe007e1 0x3ffffffffff003f0

def z418 : W := mkw 0x13dc0df7a1de835e 0x09ee06fbd0ef41af 0xf7fc1fff81fe07ff 0xfbfe0fffc0ff03ff

def z419 : W := mkw 0x00004d8ae00a800a 0x000026c570054005 0xdc84ff9ff01e001e 0xee427fcff80f000f

def z420 : W := mkw 0x4782c0585b406ee0 0x23c1602c2da03770 0x250300787f803fe1 0x1281803c3fc01ff0

def z421 : W := mkw 0x9df792750c000000 0x4efbc93a86000000 0x75ff007f8e000000 0x3aff803fc7000000

def z422 : W := mkw 0x05b3d87e6c000000 0x02d9ec3f36000000 0x7dfbfc7e7e000000 0x3efdfe3f3f000000

def z423 : W := mkw 0x0000000000000000 0x0000000000000000 0x5600000600180418 0xab000003000c020c

def z424 : W := mkw 0x09efff8af1fff42a 0x84f7ffc578fffa15 0x7bffff8071fff800 0x3dffffc038fffc00

def z425 : W := mkw 0x4600405848000260 0x2300202c24000130 0x0000001800000060 0x0000000c00000030

def z426 : W := mkw 0x67a3fc5a7f69fee8 0x33d1fe2d3fb4ff74 0x6f83fc787fe1ffe1 0x37c1fe3c3ff0fff0

def z427 : W := mkw 0x00000c0220088008 0x0000060110044004 0x10001c0600180018 0x88000e03000c000c

def z428 : W := mkw 0x4602e0585a216ee0 0x2301702c2d10b770 0x0c03e0787e01ffe1 0x0601f03c3f00fff0

def z429 : W := mkw 0x0182a00001612000 0x00c1500000b09000 0x0080e00000600000 0x0040700000300000

def z430 : W := mkw 0x460000500a000ac0 0x2300002805000560 0x000000600e000381 0x00000030070001c0

def z431 : W := mkw 0x20211c023608dc88 0x10108e011b046e44 0x5e031c067e19fc18 0xaf018e033f0cfe0c

def z432 : W := mkw 0x0200005000000240 0x0100002800000120 0x04000078000007e1 0x0200003c000003f0

def z433 : W := mkw 0x00002d82b02bc42a 0x000016c15815e215 0x92041f87807fc47e 0xc9020fc3c03fe23f

def z434 : W := mkw 0x0000490af000442a 0x0000248578002215 0xd684001ff07e047e 0xeb42000ff83f023f

def z435 : W := mkw 0x0021100000000000 0x0010880000000000 0x797b1c0000000000 0x3cbd8e0000000000

def z436 : W := mkw 0x9ff7db7fed440244 0x4ffbedbff6a20122 0xfdfffffffe660066 0x7effffffff330033

def z437 : W := mkw 0x09efb20001f53000 0x84f7d90000fa9800 0x6bfbe00001e1f800 0x35fdf00000f0fc00

def z438 : W := mkw 0x0000490af000442a 0x0000248578002215 0xdc84ff9ff000047e 0xee427fcff800023f

def z439 : W := mkw 0x09ef9680009e9000 0x84f7cb40004f4800 0x79ffff80001e0000 0x3cffffc0000f0000

def z440 : W := mkw 0x0380005001400240 0x01c0002800a00120 0x2100006001800381 0x1080003000c001c0

def z441 : W := mkw 0xbdfffffffebbddba 0x5effffffff5deedd 0xffffffffffffffff 0xffffffffffffffff

def z442 : W := mkw 0x5ffff6fd5bfffff4 0xaffffb7eadfffffa 0xffffffffffffffff 0xffffffffffffffff

def z443 : W := mkw 0x09e7ff8af02bc42a 0x04f3ffc57815e215 0xffffff9ff07fc47e 0xffffffcff83fe23f

def z444 : W := mkw 0xdff7fb7fed612260 0x6ffbfdbff6b09130 0x7dfffffffe600060 0x3effffffff300030

def z445 : W := mkw 0x9dffdb7fedd43000 0xceffedbff6ea1800 0x7dffffffff803800 0x3effffffffc01c00

def z446 : W := mkw 0x09cea28001f72000 0x84e7514000fb9000 0x73fce38001fe0000 0x39fe71c000ff0000

def z447 : W := mkw 0x0200000001400240 0x0100000000a00120 0x0200000001e007e1 0x0100000000f003f0

def z448 : W := mkw 0x0582c05848000000 0x02c1602c24000000 0x0080e01800000000 0x0040700c00000000

def z449 : W := mkw 0x11d4497fe0000000 0x08ea24bff0000000 0x7dfcfffff0000000 0x3efe7ffff8000000

def z450 : W := mkw 0x00000480000a800a 0x0000024000054005 0x80000000001e001e 0xc0000000000f000f

def z451 : W := mkw 0x987d1b27a4940114 0x4c3e8d93d24a008a 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z452 : W := mkw 0x00000902a000000a 0x0000048150000005 0x800000078000001e 0xc0000003c000000f

def z453 : W := mkw 0x0380605851614660 0x01c0302c28b0a330 0x6f80e07871e1c7e1 0x37c0703c38f0e3f0

def z454 : W := mkw 0xdffffffffffffee0 0xefffffffffffff70 0x7fffffffffffffe1 0x3ffffffffffffff0

def z455 : W := mkw 0x9df7ffffec2b8000 0x4efbfffff615c000 0x7ffffffffe7fc000 0x3fffffffff3fe000

def z456 : W := mkw 0x0208248011ffc77e 0x0104124008ffe3bf 0x8200000001ffc7ff 0xc100000000ffe3ff

def z457 : W := mkw 0x9df7d27d4c000000 0x4efbe93ea6000000 0x6dfbe0787e000000 0x36fdf03c3f000000

def z458 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x5e00ff867019c418 0xaf007fc3380ce20c

def z459 : W := mkw 0x0018002412904d90 0x000c0012094826c8 0x7f7b00667f99ff99 0xbfbd80333fccffcc

def z460 : W := mkw 0x4582e0585a216ca0 0x22c1702c2d10b650 0x6d83e0787e01f800 0x36c1f03c3f00fc00

def z461 : W := mkw 0x09e7b28001672000 0x84f3d94000b39000 0x79ffff8000660000 0x3cffffc000330000

def z462 : W := mkw 0xdfc6e359db616ee0 0x6fe371acedb0b770 0x6f87e3f9ffe1ffe1 0x37c3f1fcfff0fff0

def z463 : W := mkw 0x000000001000442a 0x0000000008002215 0x800000000000047e 0xc00000000000023f

def z464 : W := mkw 0x4402ed8afa2becaa 0x220176c57d15f655 0x0803ff807e01f800 0x0401ffc03f00fc00

def z465 : W := mkw 0x0582c95ae8000000 0x02c164ad74000000 0x7d87fffffe000000 0x3ec3ffffff000000

def z466 : W := mkw 0x20311c263608dd98 0x10188e131b046ecc 0x0c031c667e01ff99 0x86018e333f00ffcc

def z467 : W := mkw 0x12106dfff02bc77e 0x090836fff815e3bf 0xde84fffff07fc7ff 0xef427ffff83fe3ff

def z468 : W := mkw 0x13dc497fe1d40354 0x09ee24bff0ea01aa 0xfffcfffff1fe07ff 0xfffe7ffff8ff03ff

def z469 : W := mkw 0x9df7d37dcc000000 0x4efbe9bee6000000 0x21ffe3f98e000000 0x10fff1fcc7000000

def z470 : W := mkw 0x0823ff8af02bf42a 0x8411ffc57815fa15 0xde87ff9ff07ffc7e 0xef43ffcff83ffe3f

def z471 : W := mkw 0x0182ed8af16be42a 0x00c176c578b5f215 0xff87ff9ff1fffc7e 0xffc3ffcff8fffe3f

def z472 : W := mkw 0x0000000012004c80 0x0000000009002640 0x020000000181ff81 0x0100000000c0ffc0

def z473 : W := mkw 0x00000c023008c408 0x0000060118046204 0x08001c007001c000 0x04000e003800e000

def z474 : W := mkw 0x086d368000bf9000 0x84369b40005fc800 0x5afcff80007fc000 0x2d7e7fc0003fe000

def z475 : W := mkw 0x0000208001672000 0x8000104000b39000 0x0000000000660000 0x0000000000330000

def z476 : W := mkw 0x9dffdb7fec900110 0x4effedbff6480088 0x7fffffffff980799 0xbfffffffffcc03cc

def z477 : W := mkw 0x33fd7dfff7ffdffe 0x19febefffbffefff 0xffffffffffffffff 0xffffffffffffffff

def z478 : W := mkw 0x0002a00000212000 0x0001500000109000 0x0803e0000001f800 0x0401f0000000fc00

def z479 : W := mkw 0x57dc407d5bd44ff4 0x2bee203eadea27fa 0xf7fc007ffffe07ff 0xfbfe003fffff03ff

def z480 : W := mkw 0x1218007501d40354 0x090c003a80ea01aa 0x8600007f81fe07ff 0xc300003fc0ff03ff

def z481 : W := mkw 0x478040585b404ee0 0x23c0202c2da02770 0x678000787fe007e1 0x33c0003c3ff003f0

def z482 : W := mkw 0x2008248013fffd98 0x9004124009fffecc 0x0200000001ffff99 0x8100000000ffffcc

def z483 : W := mkw 0x0018002400900110 0x000c001200480088 0x2178006001800381 0x10bc003000c001c0

def z484 : W := mkw 0xbdffdb7fee901990 0x5effedbff7480cc8 0x7dffffffff803b81 0x3effffffffc01dc0

def z485 : W := mkw 0x2823be82362bfc88 0x9411df411b15fe44 0x0803ff807e01f800 0x0401ffc03f00fc00

def z486 : W := mkw 0x09e7920000000000 0x04f3c90000000000 0x217b000000000000 0x10bd800000000000

def z487 : W := mkw 0x20395d2ef698dd98 0x101cae977b4c6ecc 0x7fffffffff99ff99 0xbfffffffffccffcc

def z488 : W := mkw 0x01cc6d8af1ffc42a 0x00e636c578ffe215 0xfffcff9ff1ffc47e 0xfffe7fcff8ffe23f

def z489 : W := mkw 0x004c000000940000 0x00260000004a0000 0x107c0000001e0000 0x083e0000000f0000

def z490 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x8600001ff07fc47e 0xc300000ff83fe23f

def z491 : W := mkw 0x9dffdb7fec940114 0x4effedbff64a008a 0xfdfffffffe1e001e 0xfeffffffff0f000f

def z492 : W := mkw 0x2039102404901110 0x101c881202480888 0x0078000000000000 0x003c000000000000

def z493 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x8c00ff9ff001c47e 0xc6007fcff800e23f

def z494 : W := mkw 0x287d1ea6369edd98 0x943e8f531b4f6ecc 0x7f7f1fe67f9fff99 0xbfbf8ff33fcfffcc

def z495 : W := mkw 0x1bff927501d40354 0x0dffc93a80ea01aa 0xffffffff81fe07ff 0xffffffffc0ff03ff

def z496 : W := mkw 0x20391c2624989118 0x101c8e13124c488c 0x7d7b1c667e180018 0xbebd8e333f0c000c

def z497 : W := mkw 0x460060585a214ee0 0x2300302c2d10a770 0x4e80e0787e61c7e1 0x2740703c3f30e3f0

def z498 : W := mkw 0x0000600840210020 0x0000300420108010 0x0080e01800600060 0x0040700c00300030

def z499 : W := mkw 0x09efff8ae1ffb000 0x84f7ffc570ffd800 0x7fffff9ff1fff800 0x3fffffcff8fffc00

def z500 : W := mkw 0x23b91c7637d8dfd8 0x11dc8e3b1bec6fec 0x7ffb1c7e7ff9fff9 0xbffd8e3f3ffcfffc

def z501 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x2903e0607f81fb81 0x1481f0303fc0fdc0

def z502 : W := mkw 0x2000000012004d98 0x10000000090026cc 0x0000000000000799 0x80000000000003cc

def z503 : W := mkw 0x9df79b77ac000000 0x4efbcdbbd6000000 0x317f1fe78e000000 0x18bf8ff3c7000000

def z504 : W := mkw 0x4fef92500bd43ac0 0xa7f7c92805ea1d60 0x217b00600f803b81 0x10bd803007c01dc0

def z505 : W := mkw 0x77fffc7f7ffdfffc 0x3bfffe3fbffefffe 0xfffffc7fffffffff 0xfffffe3fffffffff

def z506 : W := mkw 0x09c6e388c1672022 0x84e371c460b39011 0x8084e39980660066 0x404271ccc0330033

def z507 : W := mkw 0xcfa3fb5aff616ee0 0x67d1fdad7fb0b770 0x6f83fff87fe1ffe1 0x37c1fffc3ff0fff0

def z508 : W := mkw 0xdff792750f402ac0 0x6ffbc93a87a01560 0x217b00600f803b81 0x10bd803007c01dc0

def z509 : W := mkw 0x09ef920001d43000 0x84f7c90000ea1800 0x79ffff8001803800 0x3cffffc000c01c00

def z510 : W := mkw 0x0008248001ffb000 0x8004124000ffd800 0x5a84ff8001fff800 0x2d427fc000fffc00

def z511 : W := mkw 0xdff7f27d5f616ee0 0x6ffbf93eafb0b770 0x6ffbe0787fe1ffe1 0x37fdf03c3ff0fff0

def z512 : W := mkw 0x29efb68013fffd98 0x94f7db4009fffecc 0x7bffff8001ffff99 0xbdffffc000ffffcc

def z513 : W := mkw 0x42002480136beeea 0x2100124009b5f775 0x8200000001ffffff 0xc100000000ffffff

def z514 : W := mkw 0x00006588c02b8022 0x000032c46015c011 0xda84ff99807fc066 0x6d427fccc03fe033

def z515 : W := mkw 0x20211c023608dc88 0x10108e011b046e44 0x6f031c607f81ff81 0x37818e303fc0ffc0

def z516 : W := mkw 0x4782e95afb616eea 0x23c174ad7db0b775 0xef83e07fffe1ffff 0xf7c1f03ffff0ffff

def z517 : W := mkw 0x8c2392000c000000 0x4611c90006000000 0x000300000e000000 0x0001800007000000

def z518 : W := mkw 0x479ae07c5bf16ff0 0x23cd703e2df8b7f8 0x7ffbe07e7ff9fff9 0xbffdf03f3ffcfffc

def z519 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x12781c060199ff99 0x893c0e0300ccffcc

def z520 : W := mkw 0x20397daef6bbddba 0x101cbed77b5deedd 0x7f7bffe67f99ff99 0xbfbdfff33fccffcc

def z521 : W := mkw 0x00391c2624989000 0x001c8e13124c4800 0x7f7b1c667f99f800 0x3fbd8e333fccfc00

def z522 : W := mkw 0x8da3db5aec000000 0x46d1edad76000000 0x6d83fff87e000000 0x36c1fffc3f000000

def z523 : W := mkw 0x0398007401d00350 0x01cc003a00e801a8 0x77f8007e01f807f9 0xbbfc003f00fc03fc

def z524 : W := mkw 0x00002c82302bc408 0x000016411815e204 0x5e84ff86707fc418 0xaf427fc3383fe20c

def z525 : W := mkw 0x1390007501400354 0x09c8003a80a001aa 0xe780007f81e007ff 0xf3c0003fc0f003ff

def z526 : W := mkw 0x09ed168001de9000 0x84f68b4000ef4800 0x73fc1f8001fe0000 0x39fe0fc000ff0000

def z527 : W := mkw 0x0208000001d40354 0x0104000000ea01aa 0x0000000001800381 0x0000000000c001c0

def z528 : W := mkw 0x4200000003402ac0 0x2100000001a01560 0x0000000001803b81 0x0000000000c01dc0

def z529 : W := mkw 0x94106dfffc2bc42a 0x4a0836fffe15e215 0xde84fffffe7fc47e 0xef427fffff3fe23f

def z530 : W := mkw 0x46006ddafa2bceea 0x230036ed7d15e775 0xde84fffffe7fc7ff 0xef427fffff3fe3ff

def z531 : W := mkw 0x0182800001402000 0x00c1400000a01000 0x2103000001803800 0x1081800000c01c00

def z532 : W := mkw 0x4402e0085a216ca0 0x220170042d10b650 0x4e83e0187e61fc60 0x2741f00c3f30fe30

def z533 : W := mkw 0x32391c773698dfdc 0x191c8e3b9b4c6fee 0xff7b1c7fff99ffff 0xffbd8e3fffccffff

def z534 : W := mkw 0x4782ec5a7b69eee8 0x23c1762d3db4f774 0x7f83fc7e7ff9fff9 0xbfc1fe3f3ffcfffc

def z535 : W := mkw 0xbdfffffffffffd98 0xdefffffffffffecc 0x7fffffffffffff99 0xbfffffffffffffcc

def z536 : W := mkw 0x4782eddaf96be66a 0x23c176ed7cb5f335 0xde84ff9ff07fc47e 0xef427fcff83fe23f

def z537 : W := mkw 0x105c002500940114 0x082e0012804a008a 0x0078000000000000 0x003c000000000000

def z538 : W := mkw 0x29ff9e2637dcfd98 0x94ffcf131bee7ecc 0x7f7b1c667f99ff99 0xbfbd8e333fccffcc

def z539 : W := mkw 0x0000000000000000 0x0000000000000000 0x4680001800600460 0x2340000c00300230

def z540 : W := mkw 0x67bbfdfefffbfffa 0x33ddfeff7ffdfffd 0xffffffffffffffff 0xffffffffffffffff

def z541 : W := mkw 0xbdff9e773e98dd98 0x5effcf3b9f4c6ecc 0x7f7b1c667f99ff99 0xbfbd8e333fccffcc

def z542 : W := mkw 0x0182e00851616420 0x00c1700428b0b210 0x6f83e01871e1fc60 0x37c1f00c38f0fe30

def z543 : W := mkw 0x00006188c0230022 0x000030c460118011 0x0000e38000000000 0x000071c000000000

def z544 : W := mkw 0x0008040000989000 0x00040200004c4800 0x020000000199f800 0x0100000000ccfc00

def z545 : W := mkw 0x203914241698dd98 0x101c8a120b4c6ecc 0x237b00600f99ff99 0x91bd803007ccffcc

def z546 : W := mkw 0x03806ddaf16bc66a 0x01c036ed78b5e335 0xff84fffff1ffc7ff 0xffc27ffff8ffe3ff

def z547 : W := mkw 0x00000480000a8000 0x0000024000054000 0x10041f80001e0000 0x08020fc0000f0000

def z548 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0xb17c0067819e039f 0xd8be0033c0cf01cf

def z549 : W := mkw 0x20291c023698dd98 0x10148e011b4c6ecc 0x0a031c007f99ff99 0x85018e003fccffcc

def z550 : W := mkw 0x9df7fffffc2bc42a 0x4efbfffffe15e215 0x7dfffffffe01c000 0x3effffffff00e000

def z551 : W := mkw 0x13dc24f511ffc77e 0x09ee127a88ffe3bf 0xf7fc007f81ffc7ff 0xfbfe003fc0ffe3ff

def z552 : W := mkw 0x11d46dfff02bc42a 0x08ea36fff815e215 0xfffcfffff07fc47e 0xfffe7ffff83fe23f

def z553 : W := mkw 0x00000902a0000000 0x0000048150000000 0x10041f8780000000 0x08020fc3c0000000

def z554 : W := mkw 0x9df7db7ffe004c80 0x4efbedbfff002640 0x7fffffffff81ff81 0x3fffffffffc0ffc0

def z555 : W := mkw 0x00006588d02bc42a 0x000032c46815e215 0x8284e399807fc47e 0xc14271ccc03fe23f

def z556 : W := mkw 0x4befb68013fffee0 0xa5f7db4009ffff70 0x7bffff8001ffffe1 0x3dffffc000fffff0

def z557 : W := mkw 0x1210007500000354 0x0908003a800001aa 0xd684007f807e07ff 0xeb42003fc03f03ff

def z558 : W := mkw 0x2010082624000118 0x100804131200008c 0x0000000600000018 0x800000030000000c

def z559 : W := mkw 0x0031182624000000 0x00188c1312000000 0x10781c0600000000 0x083c0e0300000000

def z560 : W := mkw 0x9df792750c000000 0x4efbc93a86000000 0x79ffffe00e000000 0x3cfffff007000000

def z561 : W := mkw 0x20106daef62bcdba 0x100836d77b15e6dd 0xde84fffffe7fc7ff 0xef427fffff3fe3ff

def z562 : W := mkw 0x0380005001400240 0x01c0002800a00120 0x0080001800600060 0x0040000c00300030

def z563 : W := mkw 0x4208200013f56ff4 0x2104100009fab7fa 0x8200000001ffffff 0xc100000000ffffff

def z564 : W := mkw 0x00000d82a00a800a 0x000006c150054005 0xd6841f9f807e047e 0xeb420fcfc03f023f

def z565 : W := mkw 0x0029348001ffb000 0x80149a4000ffd800 0x7b7b1c0001fff800 0x3dbd8e0000fffc00

def z566 : W := mkw 0x9dc6825108000000 0x4ee3412884000000 0x0000000000000000 0x0000000000000000

def z567 : W := mkw 0x09efbf82a1ffb00a 0x84f7dfc150ffd805 0xfbffff8781fff81e 0xfdffffc3c0fffc0f

def z568 : W := mkw 0x0021140000089000 0x00108a0000044800 0x08031c000001f800 0x04018e000000fc00

def z569 : W := mkw 0x57d6e07d5b616ee0 0x2beb703eadb0b770 0x7fffe07fffe1ffe1 0x3ffff03ffff0fff0

def z570 : W := mkw 0xddf7fb7ffe216ca0 0x6efbfdbfff10b650 0x7dfffffffe01f800 0x3effffffff00fc00

def z571 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x8a00ff80707fc47e 0xc5007fc0383fe23f

def z572 : W := mkw 0x2039182636905d98 0x101c8c131b482ecc 0x257b00667f803f99 0x92bd80333fc01fcc

def z573 : W := mkw 0x13dc24f501ffb354 0x89ee127a80ffd9aa 0xf7fc007f81ffffff 0xfbfe003fc0ffffff

def z574 : W := mkw 0x0000018080020002 0x000000c040010001 0x8004038180060006 0x400201c0c0030003

def z575 : W := mkw 0x0008000001d40000 0x0004000000ea0000 0x0200000001fe0000 0x0100000000ff0000

def z576 : W := mkw 0x9df7fbffed672000 0xcefbfdfff6b39000 0x7dfffffffe660000 0x3effffffff330000

def z577 : W := mkw 0x09cea68001ffb000 0x84e7534000ffd800 0x0284e38001fff800 0x014271c000fffc00

def z578 : W := mkw 0x9dc6e3d9c9672000 0xcee371ece4b39000 0x0084e39980660000 0x004271ccc0330000

def z579 : W := mkw 0x98751b27a4000000 0x4c3a8d93d2000000 0x7d7f1fe7fe000000 0x3ebf8ff3ff000000

def z580 : W := mkw 0x47cee0585bf56ee0 0x23e7702c2dfab770 0x7fffe0787fffffe1 0x3ffff03c3ffffff0

def z581 : W := mkw 0x4000200012216ca0 0x200010000910b650 0x000000000001f800 0x000000000000fc00

def z582 : W := mkw 0x086d1680009e9000 0x84368b40004f4800 0x7b7f1f80019ff800 0x3dbf8fc000cffc00

def z583 : W := mkw 0x00002480002bb000 0x800012400015d800 0x000000000001f800 0x000000000000fc00

def z584 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x4e80ff987061c460 0x27407fcc3830e230

def z585 : W := mkw 0x0000040000088000 0x0000020000044000 0x5a001c000019c000 0x2d000e00000ce000

def z586 : W := mkw 0x09ef920001d43000 0x84f7c90000ea1800 0x73ff000001fe3800 0x39ff800000ff1c00

def z587 : W := mkw 0x9dd6cb7fec000000 0x4eeb65bff6000000 0x0484e3fffe000000 0x024271ffff000000

def z588 : W := mkw 0x201804241298dd98 0x100c0212094c6ecc 0x777800660199ff99 0xbbbc003300ccffcc

def z589 : W := mkw 0xcc23fb0afe216ca0 0x6611fd857f10b650 0x0803ff807e01f800 0x0401ffc03f00fc00

def z590 : W := mkw 0x20080c023298dd98 0x10040601194c6ecc 0x5e001c067199ff99 0xaf000e0338ccffcc

def z591 : W := mkw 0x9dff92750dd43000 0xceffc93a86ea1800 0x217b00600f803800 0x10bd803007c01c00

def z592 : W := mkw 0x2010082636004d98 0x100804131b0026cc 0x6f0300667f81ff99 0xb78180333fc0ffcc

def z593 : W := mkw 0x09e7b680016fb000 0x84f3db4000b7d800 0x0887ff800067f800 0x0443ffc00033fc00

def z594 : W := mkw 0x0029100000901000 0x0014880000480800 0x217b000001803800 0x10bd800000c01c00

def z595 : W := mkw 0x00004d0af008c408 0x0000268578046204 0x5e84ff9ff019c418 0xaf427fcff80ce20c

def z596 : W := mkw 0x105c002500940114 0x082e0012804a008a 0xd6fc001f807e047e 0xeb7e000fc03f023f

def z597 : W := mkw 0x62393c2637f9fff8 0x311c9e131bfcfffc 0x7f7b1c667ff9fff9 0xbfbd8e333ffcfffc

def z598 : W := mkw 0x00186daef0bbc53a 0x000c36d7785de29d 0xfffcfffff1ffc7ff 0xfffe7ffff8ffe3ff

def z599 : W := mkw 0x00002480102bc42a 0x000012400815e215 0xd684001f807fc47e 0xeb42000fc03fe23f

def z600 : W := mkw 0x0000208000230000 0x0000104000118000 0x0084e38000660000 0x004271c000330000

def z601 : W := mkw 0x9c33db7fec000000 0x4e19edbff6000000 0x0c03fffffe000000 0x0601ffffff000000

def z602 : W := mkw 0x4582e0085b616ca0 0x22c170042db0b650 0x6b83e0007fe1f800 0x35c1f0003ff0fc00

def z603 : W := mkw 0x15d6c07d48000000 0x0aeb603ea4000000 0x7dffe07ffe000000 0x3efff03fff000000

def z604 : W := mkw 0x13dc607d51f54774 0x09ee303ea8faa3ba 0xfffce07ff1ffc7ff 0xfffe703ff8ffe3ff

def z605 : W := mkw 0x9dffb6f50dffb000 0xceffdb7a86ffd800 0x7bffffe00ffff800 0x3dfffff007fffc00

def z606 : W := mkw 0x0823920000000000 0x0411c90000000000 0x0803ff8000000000 0x0401ffc000000000

def z607 : W := mkw 0x57de80750bd42bd4 0x2bef403a85ea15ea 0x217b00600f803b81 0x10bd803007c01dc0

def z608 : W := mkw 0x9dc6efdbf82bc42a 0x4ee377edfc15e215 0xde84ff9ff07fc47e 0xef427fcff83fe23f

def z609 : W := mkw 0x0865120000000000 0x0432890000000000 0x107c1f8000000000 0x083e0fc000000000

def z610 : W := mkw 0x00002c82302bc42a 0x000016411815e215 0xde001c06707fc47e 0xef000e03383fe23f

def z611 : W := mkw 0x2010002406000990 0x10080012030004c8 0x000000600e000381 0x00000030070001c0

def z612 : W := mkw 0x21fd1c2637dcdd98 0x10fe8e131bee6ecc 0x7fff1c667fffff99 0xbfff8e333fffffcc

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x8400001f8000047e 0xc200000fc000023f

def z614 : W := mkw 0x0823b680002bb000 0x8411db400015d800 0x5a87ff80007ff800 0x2d43ffc0003ffc00

def z615 : W := mkw 0x42006d8af36beeea 0x210036c579b5f775 0xde84ff9ff1ffffff 0xef427fcff8ffffff

def z616 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x237b000001fff800 0x11bd800000fffc00

def z617 : W := mkw 0x4782e95afb616ee0 0x23c174ad7db0b770 0x7f87ffffffe1ffe1 0x3fc3fffffff0fff0

def z618 : W := mkw 0x90100927a4000000 0x48080493d2000000 0x0000000780000000 0x00000003c0000000

def z619 : W := mkw 0x09efb28001f73000 0x84f7d94000fb9800 0x21ffe38001e63800 0x10fff1c000f31c00

def z620 : W := mkw 0x000004001008c408 0x0000020008046204 0x020000000019c418 0x81000000000ce20c

def z621 : W := mkw 0x0000200001612000 0x0000100000b09000 0x0200000001e1f800 0x0100000000f0fc00

def z622 : W := mkw 0x478ae4d85bfffee0 0xa3c5726c2dffff70 0x6f83e0787fffffe1 0x37c1f03c3ffffff0

def z623 : W := mkw 0x9df7fb7ffc214420 0x4efbfdbffe10a210 0x7ffffffffe61c460 0x3fffffffff30e230

def z624 : W := mkw 0x0010082624000000 0x0008041312000000 0x040000667e000000 0x020000333f000000

def z625 : W := mkw 0x478280500b402ac0 0x23c1402805a01560 0x678300780fe03fe1 0x33c1803c07f01ff0

def z626 : W := mkw 0x0010002400000110 0x0008001200000088 0x0400006600000799 0x82000033000003cc

def z627 : W := mkw 0x8c23ff8aec2bb000 0xc611ffc57615d800 0x0803ff807e01f800 0x0401ffc03f00fc00

def z628 : W := mkw 0x20217d8af62bdcaa 0x1010bec57b15ee55 0xde87ff9ffe7ffc7e 0xef43ffcfff3ffe3f

def z629 : W := mkw 0x20391c2624989118 0x101c8e13124c488c 0x77781c6601980799 0xbbbc0e3300cc03cc

def z630 : W := mkw 0x02086d8af1ffc77e 0x010436c578ffe3bf 0xde84ff9ff1ffc7ff 0xef427fcff8ffe3ff

def z631 : W := mkw 0x53dc207513f56ff4 0x29ee103a89fab7fa 0xf7fc007f81ffffff 0xfbfe003fc0ffffff

def z632 : W := mkw 0x283bbea636bbfd98 0x941ddf531b5dfecc 0x7f7bffe67f99ff99 0xbfbdfff33fccffcc

def z633 : W := mkw 0x9df7fb7fed612000 0x4efbfdbff6b09000 0x7fffffffffe1f800 0x3ffffffffff0fc00

def z634 : W := mkw 0xbdff92750e901990 0x5effc93a87480cc8 0x217b00600f803b81 0x10bd803007c01dc0

def z635 : W := mkw 0x01cc248001ff8000 0x00e6124000ffc000 0x7bfcff8001ffc000 0x3dfe7fc000ffe000

def z636 : W := mkw 0x2000080236004c88 0x100004011b002644 0x000000007e000000 0x000000003f000000

def z637 : W := mkw 0x13dc0c7731dcc75c 0x09ee063b98ee63ae 0xfffc1c7ff1ffc7ff 0xfffe0e3ff8ffe3ff

def z638 : W := mkw 0x9df7fbffec230022 0x4efbfdfff6118011 0xfdfffffffe660066 0x7effffffff330033

def z639 : W := mkw 0x0382a05001612240 0x01c1502800b09120 0x6f83e07801e1ffe1 0x37c1f03c00f0fff0

def z640 : W := mkw 0x4feff6d849ffb260 0xa7f7fb6c24ffd930 0x7bffff9801fff860 0x3dffffcc00fffc30

def z641 : W := mkw 0x13d4007501440354 0x09ea003a80a201aa 0x8484007f806607ff 0xc242003fc03303ff

def z642 : W := mkw 0x307d1c27369cdd9c 0x183e8e139b4e6ece 0xff7f1c67ff9fff9f 0xffbf8e33ffcfffcf

def z643 : W := mkw 0x19ffb6f501ffb000 0x8cffdb7a80ffd800 0x7fffffff81fff800 0x3fffffffc0fffc00

def z644 : W := mkw 0x0180000001400000 0x00c0000000a00000 0x6380000001e00000 0x31c0000000f00000

def z645 : W := mkw 0x00004d8af00ac42a 0x000026c578056215 0x94041f9ff01e047e 0xca020fcff80f023f

def z646 : W := mkw 0x03cc005001d40240 0x01e6002800ea0120 0x77fc007801fe07e1 0x3bfe003c00ff03f0

def z647 : W := mkw 0x13c4005101440244 0x09e2002880a20122 0xe784007981e607e7 0x73c2003cc0f303f3

def z648 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0x75fc007f81800381 0x3afe003fc0c001c0

def z649 : W := mkw 0x00002d82a02b800a 0x000016c15015c005 0xda84ff87807fc01e 0xed427fc3c03fe00f

def z650 : W := mkw 0x1210007500000354 0x0908003a800001aa 0x0000006000000381 0x00000030000001c0

def z651 : W := mkw 0x29ff922407d43990 0x94ffc91203ea1cc8 0x217b00600f803b81 0x10bd803007c01dc0

def z652 : W := mkw 0x9bfd1b77a5d40354 0x4dfe8dbbd2ea01aa 0xf7fc1fff81fe07ff 0xfbfe0fffc0ff03ff

def z653 : W := mkw 0x13d4007501440244 0x09ea003a80a20122 0xf5fc007f80660066 0x7afe003fc0330033

def z654 : W := mkw 0x09e7db0ae0000000 0x04f3ed8570000000 0x7dffff9ff0000000 0x3effffcff8000000

def z655 : W := mkw 0x6208240013f9fff8 0x3104120009fcfffc 0x0200000001f9fff9 0x8100000000fcfffc

def z656 : W := mkw 0x9ffffffffdffc77e 0x4ffffffffeffe3bf 0xffffffffffffc7ff 0xffffffffffffe3ff

def z657 : W := mkw 0x01cc000001d40000 0x00e6000000ea0000 0xf7fc001f81fe047e 0xfbfe000fc0ff023f

def z658 : W := mkw 0x09ef960001dcb000 0x84f7cb0000ee5800 0x7b7b1c000199f800 0x3dbd8e0000ccfc00

def z659 : W := mkw 0x00002480102bc42a 0x000012400815e215 0xda84ff80007fc47e 0xed427fc0003fe23f

def z660 : W := mkw 0x20391c2624989118 0x101c8e13124c488c 0x7b7b1c060199f818 0xbdbd8e0300ccfc0c

def z661 : W := mkw 0x25bbdc7e7e98dd98 0x12ddee3f3f4c6ecc 0x7ffbfc7e7f99ff99 0xbffdfe3f3fccffcc

def z662 : W := mkw 0x99ffbfa7a5ffb000 0xccffdfd3d2ffd800 0x7bffff8781fff800 0x3dffffc3c0fffc00

def z663 : W := mkw 0x4402e00848212020 0x2201700424109010 0x0000e00000000000 0x0000700000000000

def z664 : W := mkw 0x20395d2ef698ddba 0x101cae977b4c6edd 0xff7b1c7fff99ffff 0xffbd8e3fffccffff

def z665 : W := mkw 0x57dee07d5bf56ff4 0x2bef703eadfab7fa 0x6ffbe0787fe1ffe1 0x37fdf03c3ff0fff0

def z666 : W := mkw 0x2021100006001880 0x1010880003000c40 0x000300000e003800 0x0001800007001c00

def z667 : W := mkw 0x0844028000060000 0x8422014000030000 0x0004038000060000 0x000201c000030000

def z668 : W := mkw 0xdffffb7ffff56ff4 0x6ffffdbffffab7fa 0xffffffffffffffff 0xffffffffffffffff

def z669 : W := mkw 0x0000000000000000 0x0000000000000000 0x82000000007e047e 0xc1000000003f023f

def z670 : W := mkw 0x13fd147501dc9354 0x09fe8a3a80ee49aa 0xffff1c7f81ffffff 0xffff8e3fc0ffffff

def z671 : W := mkw 0x01dc002401d40110 0x00ee001200ea0088 0x77fc006601fe0799 0xbbfe003300ff03cc

def z672 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0xa1fc007981e603e7 0x50fe003cc0f301f3

def z673 : W := mkw 0x99f79b27a4000000 0x4cfbcd93d2000000 0x79ffff8780000000 0x3cffffc3c0000000

def z674 : W := mkw 0x9de7db5bec000000 0x4ef3edadf6000000 0x0887ff99fe000000 0x0443ffccff000000

def z675 : W := mkw 0x0000600850214420 0x000030042810a210 0xde84e01ff07fc47e 0xef42700ff83fe23f

def z676 : W := mkw 0x2039142406989990 0x101c8a12034c4cc8 0x7b7b1c600f99fb81 0x3dbd8e3007ccfdc0

def z677 : W := mkw 0x00297d8af0bbd42a 0x0014bec5785dea15 0xffffff9ff1fffc7e 0xffffffcff8fffe3f

def z678 : W := mkw 0x09efbe8231fff408 0x84f7df4118fffa04 0x7fffff8671fffc18 0xbfffffc338fffe0c

def z679 : W := mkw 0x4382a00013616ee0 0x21c1500009b0b770 0x6b83e00001e1ffe1 0x35c1f00000f0fff0

def z680 : W := mkw 0x9610497fec000354 0x4b0824bff60001aa 0x8400007ffe0007ff 0xc200003fff0003ff

def z681 : W := mkw 0x01cea00001f52000 0x00e7500000fa9000 0x7bffe00001fff800 0x3dfff00000fffc00

def z682 : W := mkw 0x6610487e7e004ff8 0x3308243f3f0027fc 0x0400007e7e0007f9 0x8200003f3f0003fc

def z683 : W := mkw 0x13dc24f501ff8354 0x09ee127a80ffc1aa 0xfffcffff81ffc7ff 0xfffe7fffc0ffe3ff

def z684 : W := mkw 0x00180c263098c518 0x000c0613184c628c 0x7f781c667199c799 0xbfbc0e3338cce3cc

def z685 : W := mkw 0x9fdec37dc9d40354 0x4fef61bee4ea01aa 0xf7fce3ff81fe07ff 0xfbfe71ffc0ff03ff

def z686 : W := mkw 0x20393ca636bbdd98 0x101c9e531b5deecc 0x7fffffe67fffff99 0xbffffff33fffffcc

def z687 : W := mkw 0x4fefffdafbfffeea 0xa7f7ffed7dffff75 0xffffffffffffffff 0xffffffffffffffff

def z688 : W := mkw 0x4782e4d85b6beeea 0x23c1726c2db5f775 0xef83e0787fffffff 0xf7c1f03c3fffffff

def z689 : W := mkw 0x1054002500000000 0x082a001280000000 0x107c000780000000 0x083e0003c0000000

def z690 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0x73fc006001fe0381 0x39fe003000ff01c0

def z691 : W := mkw 0x1bfd16f501de9354 0x8dfe8b7a80ef49aa 0xf7fc1fff81fe07ff 0xfbfe0fffc0ff03ff

def z692 : W := mkw 0x4782805009402240 0x23c1402804a01120 0x0000000000000000 0x0000000000000000

def z693 : W := mkw 0x1bc6a2d101672244 0x8de3516880b39122 0x8084e39980660066 0x404271ccc0330033

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x5484001f80000000 0x2a42000fc0000000

def z695 : W := mkw 0x1218007500900354 0x090c003a804801aa 0xf778007f819807ff 0xfbbc003fc0cc03ff

def z696 : W := mkw 0x9fffdb7fedd40354 0x4fffedbff6ea01aa 0x7dffffffff800381 0x3effffffffc001c0

def z697 : W := mkw 0x4782a0501b616ee0 0x23c150280db0b770 0x230300600fe1ffe1 0x1181803007f0fff0

def z698 : W := mkw 0x8c23ff8afc2bc42a 0x4611ffc57e15e215 0xde87ff9ffe7fc47e 0xef43ffcfff3fe23f

def z699 : W := mkw 0x9df7df7ffc08c408 0x4efbefbffe046204 0x7ffffffffe19c418 0xbfffffffff0ce20c

def z700 : W := mkw 0x2039182626901990 0x101c8c1313480cc8 0x7d7b1c667f803b81 0x3ebd8e333fc01dc0

def z701 : W := mkw 0x9dffdb7fedd40000 0x4effedbff6ea0000 0x7ffffffffffe0000 0x3fffffffffff0000

def z702 : W := mkw 0x0200000000000354 0x01000000000001aa 0x80000000000007ff 0xc0000000000003ff

def z703 : W := mkw 0x0182800000000000 0x00c1400000000000 0x6983e00000000000 0x34c1f00000000000

def z704 : W := mkw 0x0031102404000000 0x0018881202000000 0x217b00600e000000 0x10bd803007000000

def z705 : W := mkw 0x6792e87e7f616ff8 0x33c9743f3fb0b7fc 0x6f83e07e7fe1fff9 0xb7c1f03f3ff0fffc

def z706 : W := mkw 0x4602e0085b616ee0 0x230170042db0b770 0x0a03e0007fe1ffe1 0x0501f0003ff0fff0

def z707 : W := mkw 0x20391ca6369add98 0x101c8e531b4d6ecc 0x7f7f1fe67f9fff99 0xbfbf8ff33fcfffcc

def z708 : W := mkw 0x01cea48001ffa000 0x00e7524000ffd000 0x7bffff8001fff800 0x3dffffc000fffc00

def z709 : W := mkw 0x0031592ee4000000 0x0018ac9772000000 0x7d7bffe67e000000 0x3ebdfff33f000000

def z710 : W := mkw 0xb410497ffe004dba 0x5a0824bfff0026dd 0x8400007ffe0007ff 0xc200003fff0003ff

def z711 : W := mkw 0xac23ff8afe2bdcaa 0x5611ffc57f15ee55 0x0803ff807e01f800 0x0401ffc03f00fc00

def z712 : W := mkw 0x20397daee4bb913a 0x101cbed7725dc89d 0x90fcff9f807e007e 0xc87e7fcfc03f003f

def z713 : W := mkw 0x99f79b27a4000000 0x4cfbcd93d2000000 0x7dffffe7fe000000 0x3efffff3ff000000

def z714 : W := mkw 0x9c755b7fec000000 0x4e3aadbff6000000 0x5cfcfffffe000000 0x2e7e7fffff000000

def z715 : W := mkw 0xdfc6e2595b616ee0 0x6fe3712cadb0b770 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z716 : W := mkw 0x5fc6e2d949672264 0xafe3716ca4b39132 0x8084e39980660066 0x404271ccc0330033

def z717 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x18ffff80007ff800 0x0c7fffc0003ffc00

def z718 : W := mkw 0x287d1fa6a49e911a 0x943e8fd3524f488d 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z719 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x397b1c667f99fb99 0x9cbd8e333fccfdcc

def z720 : W := mkw 0xd410497ffe004ca0 0x6a0824bfff002650 0x0400007ffe000000 0x0200003fff000000

def z721 : W := mkw 0x09efdb0af1d4742a 0x84f7ed8578ea3a15 0xa57b001ff1803c7e 0xd2bd800ff8c01e3f

def z722 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x7f83e07e7ff9fff9 0xbfc1f03f3ffcfffc

def z723 : W := mkw 0x57c6e1d9c9672266 0x2be370ece4b39133 0x8084e39980660066 0x404271ccc0330033

def z724 : W := mkw 0x0039182636904d90 0x001c8c131b4826c8 0x7f7b1c667f99ff99 0xbfbd8e333fccffcc

def z725 : W := mkw 0x460000501a004ec0 0x230000280d002760 0x6f0300607f81ff81 0x378180303fc0ffc0

def z726 : W := mkw 0x2010492ef6004d98 0x100824977b0026cc 0x0400007ffe000799 0x8200003fff0003cc

def z727 : W := mkw 0x9fff92750dd43354 0xcfffc93a86ea19aa 0x217b00600f803b81 0x10bd803007c01dc0

def z728 : W := mkw 0x4fc6e3d8db676ee2 0xa7e371ec6db3b771 0xef87e3f9ffe7ffe7 0x77c3f1fcfff3fff3

def z729 : W := mkw 0x082bb68000bbb000 0x8415db40005dd800 0x187bff800019f800 0x0c3dffc0000cfc00

def z730 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x6f03e0607f81ff81 0x3781f0303fc0ffc0

def z731 : W := mkw 0x09ef960001dc9000 0x04f7cb0000ee4800 0x7bffff8001fff800 0x3dffffc000fffc00

def z732 : W := mkw 0x203971acc6b319b2 0x101cb8d663598cd9 0xa1ffe3f98fe63be7 0x50fff1fcc7f31df3

def z733 : W := mkw 0xcf82e358db616ee0 0x67c171ac6db0b770 0x6f83e3f87fe1ffe1 0x37c1f1fc3ff0fff0

def z734 : W := mkw 0x545ee02d5ab56db4 0x2a2f7016ad5ab6da 0x987fe007fe1ff81e 0xcc3ff003ff0ffc0f

def z735 : W := mkw 0xda753b27b7616ee0 0x6d3a9d93dbb0b770 0x127c1f8781e1ffe1 0x093e0fc3c0f0fff0

def z736 : W := mkw 0x19efb68101ffb004 0x8cf7db4080ffd802 0xfbffff8181fff806 0x7dffffc0c0fffc03

def z737 : W := mkw 0x09efb68000bbb000 0x84f7db40005dd800 0x7bffff800199f800 0x3dffffc000ccfc00

def z738 : W := mkw 0x082bb68000bbb000 0x8415db40005dd800 0x7bffff8001fff800 0x3dffffc000fffc00

def z739 : W := mkw 0x2018082636904d98 0x100c04131b4826cc 0x7f7b00667f99ff99 0xbfbd80333fccffcc

def z740 : W := mkw 0x20391c26249c911c 0x101c8e13124e488e 0x90781c06001e001e 0xc83c0e03000f000f

def z741 : W := mkw 0x4c23ff8afa2bfcaa 0xa611ffc57d15fe55 0x0803ff807e01f800 0x0401ffc03f00fc00

def z742 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x7fffff9801fffc60 0x3fffffcc00fffe30

def z743 : W := mkw 0x47828dd2ab4aaaca 0x23c146e955a55565 0xb1071fe78f9e3b9f 0xd8838ff3c7cf1dcf

def z744 : W := mkw 0x84006d8afc2bc42a 0x420036c57e15e215 0xde84ff9ffe7fc47e 0xef427fcfff3fe23f

def z745 : W := mkw 0x0de7d20848000000 0x06f3e90424000000 0x79ffff807e000000 0x3cffffc03f000000

def z746 : W := mkw 0xa8391f26a4989118 0x541c8f93524c488c 0x10781f8600180018 0x883c0fc3000c000c

def z747 : W := mkw 0x13c4005113444ec4 0x09e2002889a22762 0xef870079ffe7ffe7 0x77c3803cfff3fff3

def z748 : W := mkw 0x0befb6d001ffb240 0x85f7db6800ffd920 0x7bffff9801fff860 0x3dffffcc00fffc30

def z749 : W := mkw 0xdfc6e359db656ee4 0x6fe371acedb2b772 0xef87e3f9ffe7ffe7 0x77c3f1fcfff3fff3

def z750 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x397fffe7fe000000 0x1cbffff3ff000000

def z751 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x18ffff9ffe000000 0x0c7fffcfff000000

def z752 : W := mkw 0x09e7b20000212000 0x04f3d90000109000 0x79ffff800001f800 0x3cffffc00000fc00

def z753 : W := mkw 0x9c77db2fec000000 0x4e3bed97f6000000 0x5cffff9ffe000000 0x2e7fffcfff000000

def z754 : W := mkw 0x09efb68000bb9000 0x04f7db40005dc800 0x7bffff8001fff800 0x3dffffc000fffc00

def z755 : W := mkw 0x9c77db2fec000000 0x4e3bed97f6000000 0x7d7fffe7fe000000 0x3ebffff3ff000000

def z756 : W := mkw 0x09efb68001ffb114 0x84f7db4000ffd88a 0xfbffff8001fff81e 0xfdffffc000fffc0f

def z757 : W := mkw 0x09e7920000000000 0x04f3c90000000000 0x7dffffe07e000000 0x3efffff03f000000

def z758 : W := mkw 0x4fc6e3d8c9672262 0xa7e371ec64b39131 0x8084e39980660066 0x404271ccc0330033

def z759 : W := mkw 0x13de807501d40354 0x09ef403a80ea01aa 0xffffe07f81fe07ff 0xfffff03fc0ff03ff

def z760 : W := mkw 0x4fc6e2585b656ee0 0xa7e3712c2db2b770 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z761 : W := mkw 0x6208248013fbfffa 0x3104124009fdfffd 0x8200000001ffffff 0xc100000000ffffff

def z762 : W := mkw 0x4f82e2d85b636ee0 0xa7c1716c2db1b770 0x6f83e3f87fe1ffe1 0x37c1f1fc3ff0fff0

def z763 : W := mkw 0x09abb68001fbb000 0x84d5db4000fdd800 0x7bfbff8001f9f800 0x3dfdffc000fcfc00

def z764 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x79ffffe07e000000 0x3cfffff03f000000

def z765 : W := mkw 0x0182800013406c80 0x00c1400009a03640 0x6f0300607f81ff81 0x378180303fc0ffc0

def z766 : W := mkw 0xcc23ff8afe2becaa 0x6611ffc57f15f655 0x0803ff807e01f800 0x0401ffc03f00fc00

def z767 : W := mkw 0x00391c263698dc80 0x001c8e131b4c6e40 0x7f7b1c667f99ff81 0x3fbd8e333fccffc0

def z768 : W := mkw 0x33e51c53374cdecc 0x19f28e299ba66f66 0x88871c19fe67f866 0x44438e0cff33fc33

def z769 : W := mkw 0x29efb68001ffb118 0x94f7db4000ffd88c 0x7bffff8001fff818 0xbdffffc000fffc0c

def z770 : W := mkw 0x09ef9680009e9000 0x84f7cb40004f4800 0x7bffff80019ff800 0x3dffffc000cffc00

def z771 : W := mkw 0x94186dffedffb000 0xca0c36fff6ffd800 0x0600007ffffff800 0x0300003ffffffc00

def z772 : W := mkw 0x4602e0085b616ee0 0x230170042db0b770 0x6f03e0607fe1ffe1 0x3781f0303ff0fff0

def z773 : W := mkw 0x97dc00750dd40354 0x4bee003a86ea01aa 0xf7fc007f8ffe07ff 0xfbfe003fc7ff03ff

def z774 : W := mkw 0x5610497ffa004ffe 0x2b0824bffd0027ff 0x8400007ffe0007ff 0xc200003fff0003ff

def z775 : W := mkw 0x00311c263608cc88 0x00188e131b046644 0x7f7b1c667f99ff99 0xbfbd8e333fccffcc

def z776 : W := mkw 0x0021100012004c80 0x0010880009002640 0x7f7b1c607f81ff81 0x3fbd8e303fc0ffc0

def z777 : W := mkw 0x0398007401d00350 0x01cc003a00e801a8 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z778 : W := mkw 0x105c002500940114 0x082e0012804a008a 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z779 : W := mkw 0xdfc6e3d9c9632262 0x6fe371ece4b19131 0x8084e39980660066 0x404271ccc0330033

def z780 : W := mkw 0x95d4497fec000000 0x4aea24bff6000000 0x7dfcfffffe000000 0x3efe7fffff000000

def z781 : W := mkw 0x0008000012904c80 0x0004000009482640 0x7f7b00607f99ff81 0x3fbd80303fccffc0

def z782 : W := mkw 0x9c33db7fec000000 0x4e19edbff6000000 0x7d7bfffffe000000 0x3ebdffffff000000

def z783 : W := mkw 0x19efb6d101ffb000 0x8cf7db6880ffd800 0x7bffff9981fff800 0x3dffffccc0fffc00

def z784 : W := mkw 0x1befb6d101ffb244 0x8df7db6880ffd922 0xfffffff981ffffe7 0x7ffffffcc0fffff3

def z785 : W := mkw 0xf610497ffe004ff8 0x7b0824bfff0027fc 0x0400007ffe0007f9 0x8200003fff0003fc

def z786 : W := mkw 0x6610497efe004ffa 0x330824bf7f0027fd 0x8400007ffe0007ff 0xc200003fff0003ff

def z787 : W := mkw 0x30391c273698dd9c 0x181c8e139b4c6ece 0xff7b1c67ff99ff9f 0xffbd8e33ffccffcf

def z788 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x29fffff9fe000000 0x14fffffcff000000

def z789 : W := mkw 0x4fc6e25849652260 0xa7e3712c24b29130 0x0080e01800600060 0x0040700c00300030

def z790 : W := mkw 0x29d6aaa637676d98 0x94eb55531bb3b6cc 0x0484e3e67e660799 0x824271f33f3303cc

def z791 : W := mkw 0x0182800012004c80 0x00c1400009002640 0x6f83e0607f81ff81 0x37c1f0303fc0ffc0

def z792 : W := mkw 0x20391da6b69add9a 0x101c8ed35b4d6ecd 0xffff1fffffffffff 0xffff8fffffffffff

def z793 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x14fcfffffe000000 0x0a7e7fffff000000

def z794 : W := mkw 0x9ff7db7fec000354 0x4ffbedbff60001aa 0x7dfffffffe000381 0x3effffffff0001c0

def z795 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x7ffffffffe7e0000 0x3fffffffff3f0000

def z796 : W := mkw 0x09efb20001f53000 0x84f7d90000fa9800 0x7bffff8001e1f800 0x3dffffc000f0fc00

def z797 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0xff87ff9ff1fffc7e 0xffc3ffcff8fffe3f

def z798 : W := mkw 0x9dc6c359da004c80 0x4ee361aced002640 0x6f87e3f9ff81ff81 0x37c3f1fcffc0ffc0

def z799 : W := mkw 0x0180000013404c80 0x00c0000009a02640 0x6f8300607fe1ff81 0x37c180303ff0ffc0

def z800 : W := mkw 0x9de7db5bec000000 0x4ef3edadf6000000 0x79ffff99fe000000 0x3cffffccff000000

def z801 : W := mkw 0x9ff7db7fed400354 0x4ffbedbff6a001aa 0xffffffffffe007ff 0xfffffffffff003ff

def z802 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x9284ff9f807fc47e 0xc9427fcfc03fe23f

def z803 : W := mkw 0x9c77db7fec000000 0x4e3bedbff6000000 0x1c7ffffffe000000 0x0e3fffffff000000

def z804 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0xfbffff8781fff81e 0xfdffffc3c0fffc0f

def z805 : W := mkw 0x4782c0585b406ec0 0x23c1602c2da03760 0x6f83e0787f81ff81 0x37c1f03c3fc0ffc0

def z806 : W := mkw 0x08339a2624000000 0x0419cd1312000000 0x7d7bffe67e000000 0x3ebdfff33f000000

def z807 : W := mkw 0x9410497ffe004c80 0x4a0824bfff002640 0x0400007ffe000781 0x0200003fff0003c0

def z808 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x7fffffe001ffff81 0x3ffffff000ffffc0

def z809 : W := mkw 0xbdcec759da98dd98 0x5ee763aced4c6ecc 0x0284e3998199ff99 0x814271ccc0ccffcc

def z810 : W := mkw 0x00004d8ae00a800a 0x000026c570054005 0xde84ff9ff07e047e 0xef427fcff83f023f

def z811 : W := mkw 0x307d1c2724989118 0x183e8e13924c488c 0x107c1c0780180018 0x883e0e03c00c000c

def z812 : W := mkw 0x09c6a28013676c80 0x84e3514009b3b640 0x6f87e3e07fe7ff81 0x37c3f1f03ff3ffc0

def z813 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x7b7bff800199f800 0x3dbdffc000ccfc00

def z814 : W := mkw 0x09e7b680016ba000 0x04f3db4000b5d000 0x7bffff8001fff800 0x3dffffc000fffc00

def z815 : W := mkw 0x20391ca6249a911a 0x101c8e53124d488d 0x90781c06001e001e 0xc83c0e03000f000f

def z816 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x277b00667f99ff99 0x93bd80333fccffcc

def z817 : W := mkw 0x082bb68001ffb000 0x8415db4000ffd800 0x7b7bff8001fff800 0x3dbdffc000fffc00

def z818 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x9884ff9ff07fc07e 0xcc427fcff83fe03f

def z819 : W := mkw 0x09e7920000000000 0x04f3c90000000000 0x7bffff800181f800 0x3dffffc000c0fc00

def z820 : W := mkw 0x8c33db2eec000000 0x4619ed9776000000 0x7dfffffffe000000 0x3effffffff000000

def z821 : W := mkw 0x4782e0d85b636ee2 0x23c1706c2db1b771 0xef83e0787fe7ffe7 0x77c1f03c3ff3fff3

def z822 : W := mkw 0xd610497ffe004ff4 0x6b0824bfff0027fa 0x8400007ffe0007ff 0xc200003fff0003ff

def z823 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0x92fc001f81fe07ff 0xc97e000fc0ff03ff

def z824 : W := mkw 0x4782e0585b656ee4 0x23c1702c2db2b772 0xef83e0787fe7ffe7 0x77c1f03c3ff3fff3

def z825 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x29ffff8001e7f800 0x14ffffc000f3fc00

def z826 : W := mkw 0x086fb68001ffb000 0x8437db4000ffd800 0x1a7fff8001fff800 0x0d3fffc000fffc00

def z827 : W := mkw 0x4782c0585b406ee0 0x23c1602c2da03770 0x6f0300787f81ffe1 0x3781803c3fc0fff0

def z828 : W := mkw 0x2823ff8af62bfcaa 0x9411ffc57b15fe55 0x0803ff807e01f800 0x0401ffc03f00fc00

def z829 : W := mkw 0x2208248013ffdffe 0x1104124009ffefff 0x8200000001ffffff 0xc100000000ffffff

def z830 : W := mkw 0x9ff7db7fed440244 0x4ffbedbff6a20122 0xffffffffffe607e7 0x7ffffffffff303f3

def z831 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0xfffcffff81fe07ff 0xfffe7fffc0ff03ff

def z832 : W := mkw 0x440280001a006c80 0x220140000d003640 0x6f0300607f81ff81 0x378180303fc0ffc0

def z833 : W := mkw 0x9defb6d109ffb000 0xcef7db6884ffd800 0x7bffff8001fff800 0x3dffffc000fffc00

def z834 : W := mkw 0x125c002501d40354 0x092e001280ea01aa 0xd6fc001f81fe07ff 0xeb7e000fc0ff03ff

def z835 : W := mkw 0x9df7db7fed402000 0x4efbedbff6a01000 0x7dffffffff803800 0x3effffffffc01c00

def z836 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x2983e0787fe1fbe1 0x14c1f03c3ff0fdf0

def z837 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x7ffffffffe180418 0xbfffffffff0c020c

def z838 : W := mkw 0x082bb68000bbb000 0x8415db40005dd800 0x297bff800181f800 0x14bdffc000c0fc00

def z839 : W := mkw 0x29ffbea625ffb118 0x94ffdf5312ffd88c 0x10fcff86007e0018 0x887e7fc3003f000c

def z840 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0xff84fffff1ffc7ff 0xffc27ffff8ffe3ff

def z841 : W := mkw 0x00006d8af22bccaa 0x000036c57915e655 0xde87ff9ffe7ffc7e 0xef43ffcfff3ffe3f

def z842 : W := mkw 0x0182e00853616ca0 0x00c1700429b0b650 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z843 : W := mkw 0x4208248013fffeea 0xa104124009ffff75 0x8200000001ffffff 0xc100000000ffffff

def z844 : W := mkw 0x2039102416905d90 0x101c88120b482ec8 0x7f7b00667f99ff99 0xbfbd80333fccffcc

def z845 : W := mkw 0x086d368001ffb000 0x84369b4000ffd800 0x5afcff8001fff800 0x2d7e7fc000fffc00

def z846 : W := mkw 0x1df7d27d48000000 0x0efbe93ea4000000 0x7dfffffffe000000 0x3effffffff000000

def z847 : W := mkw 0x4602e0585b616ee0 0x2301702c2db0b770 0x0e03e0787fe1ffe1 0x0701f03c3ff0fff0

def z848 : W := mkw 0x387d1ea7249e911c 0x9c3e8f53924f488e 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z849 : W := mkw 0x460060585b616ee0 0x2300302c2db0b770 0x6f0300787fe1ffe1 0x3781803c3ff0fff0

def z850 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x7fffff8601fffc18 0xbfffffc300fffe0c

def z851 : W := mkw 0x20391d26a4989118 0x101c8e93524c488c 0x107c1f8780180018 0x883e0fc3c00c000c

def z852 : W := mkw 0x9fc6e3d9c9672244 0xcfe371ece4b39122 0x8084e39980660066 0x404271ccc0330033

def z853 : W := mkw 0x4e6d56d85a9edee0 0xa736ab6c2d4f6f70 0x147c1ff87e1e07e1 0x0a3e0ffc3f0f03f0

def z854 : W := mkw 0x307d1da7a49e911e 0x183e8ed3d24f488f 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z855 : W := mkw 0x2008248012bbddba 0x10041240095deedd 0x020000000199ff99 0x8100000000ccffcc

def z856 : W := mkw 0x9df7db7fed400000 0x4efbedbff6a00000 0x7fffffffffe00000 0x3ffffffffff00000

def z857 : W := mkw 0xd782e159db616ee0 0x6bc170acedb0b770 0x6f83e079ffe1ffe1 0x37c1f03cfff0fff0

def z858 : W := mkw 0x09efb68000bfb000 0x84f7db40005fd800 0x79ffff80001ff800 0x3cffffc0000ffc00

def z859 : W := mkw 0x9de7d359c8000000 0x4ef3e9ace4000000 0x7dfffff9fe000000 0x3efffffcff000000

def z860 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0xfbffff9981fff866 0x7dffffccc0fffc33

def z861 : W := mkw 0x13dc6dfff1ffc77e 0x09ee36fff8ffe3bf 0x2978ffe07181c381 0x14bc7ff038c0e1c0

def z862 : W := mkw 0x0008248013fffc80 0x8004124009fffe40 0x0200000001ffff81 0x0100000000ffffc0

def z863 : W := mkw 0x0000000012004c80 0x0000000009002640 0xff87007fffffffff 0xffc3803fffffffff

def z864 : W := mkw 0x3210497ff6004ffe 0x190824bffb0027ff 0x8400007ffe0007ff 0xc200003fff0003ff

def z865 : W := mkw 0x2008248012bbdd98 0x10041240095deecc 0x0200000001ffff99 0x8100000000ffffcc

def z866 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0xfdfffffffe00047e 0xfeffffffff00023f

def z867 : W := mkw 0x9df7b6f51c2bc42a 0x4efbdb7a8e15e215 0xa37b00600e7fc47e 0xd1bd8030073fe23f

def z868 : W := mkw 0x09efb6d001ffb000 0x84f7db6800ffd800 0x7ffffff801fff800 0x3ffffffc00fffc00

def z869 : W := mkw 0x09e7b680016bb000 0x84f3db4000b5d800 0x7bffff8001e1f800 0x3dffffc000f0fc00

def z870 : W := mkw 0x00180c263298cd98 0x000c0613194c66cc 0x7f7b1c667f99ff99 0xbfbd8e333fccffcc

def z871 : W := mkw 0x1a33b6f5002bb354 0x8d19db7a8015d9aa 0x8c03ffff8001ffff 0xc601ffffc000ffff

def z872 : W := mkw 0x0000690af0214420 0x000034857810a210 0xde84ff9ff07fc47e 0xef427fcff83fe23f

def z873 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x6f7b1c607f81ff81 0x37bd8e303fc0ffc0

def z874 : W := mkw 0x2008248013fffc88 0x9004124009fffe44 0x0200000001fff800 0x0100000000fffc00

def z875 : W := mkw 0x00006d8ae02b802a 0x000036c57015c015 0xd684ff9f807e047e 0xeb427fcfc03f023f

def z876 : W := mkw 0x11f5597fe4000000 0x08faacbff2000000 0x7dfffffffe000000 0x3effffffff000000

def z877 : W := mkw 0x4208248013fffff4 0xa104124009fffffa 0x8200000001ffffff 0xc100000000ffffff

def z878 : W := mkw 0x01abb48001fbb000 0x00d5da4000fdd800 0x7bffff8001fff800 0x3dffffc000fffc00

def z879 : W := mkw 0x6423fd8afe2bfcaa 0x3211fec57f15fe55 0x0803ff807e01f800 0x0401ffc03f00fc00

def z880 : W := mkw 0x00006d8af02bf42a 0x800036c57815fa15 0xde84ff9ff07ffc7e 0xef427fcff83ffe3f

def z881 : W := mkw 0x9df7db7fec000022 0x4efbedbff6000011 0xfdfffffffe000066 0x7effffffff000033

def z882 : W := mkw 0x57c6e0595b656ee4 0x2be3702cadb2b772 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z883 : W := mkw 0x2039102416905d90 0x101c88120b482ec8 0x297b00607f81fb81 0x14bd80303fc0fdc0

def z884 : W := mkw 0x4782e0584b612ac0 0x23c1702c25b09560 0x6f83e0787fe1fb81 0x37c1f03c3ff0fdc0

def z885 : W := mkw 0x9c77db2fec000000 0x4e3bed97f6000000 0x087bff807e000000 0x043dffc03f000000

def z886 : W := mkw 0x13d4007501400240 0x09ea003a80a00120 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z887 : W := mkw 0x0029140000989000 0x00148a00004c4800 0x7bffff800199f800 0x3dffffc000ccfc00

def z888 : W := mkw 0x9ff7db7fec000354 0x4ffbedbff60001aa 0xfffffffffe7e07ff 0xffffffffff3f03ff

def z889 : W := mkw 0x13de807501d42354 0x09ef403a80ea11aa 0xf7ff007f81fe3fff 0xfbff803fc0ff1fff

def z890 : W := mkw 0x4782a0501b616ec0 0x23c150280db0b760 0x6f83e0607fe1ff81 0x37c1f0303ff0ffc0

def z891 : W := mkw 0x09e7960000089000 0x04f3cb0000044800 0x79ffff800001f800 0x3cffffc00000fc00

def z892 : W := mkw 0x09f7db2ee4000000 0x04fbed9772000000 0x7dfffffffe000000 0x3effffffff000000

def z893 : W := mkw 0x0000400852004c80 0x0000200429002640 0x6f83e0787f81ff81 0x37c1f03c3fc0ffc0

def z894 : W := mkw 0x3bff927507d43bd4 0x9dffc93a83ea1dea 0x217b00600f803b81 0x10bd803007c01dc0

def z895 : W := mkw 0x9ff7db7fed400240 0x4ffbedbff6a00120 0x7dfffffffe600060 0x3effffffff300030

def z896 : W := mkw 0x67bbfc7e6df9b378 0x33ddfe3f36fcd9bc 0x10f8fc1e00780078 0x887c7e0f003c003c

def z897 : W := mkw 0x4befb68001ffb260 0xa5f7db4000ffd930 0x7bffff8001fff860 0x3dffffc000fffc30

def z898 : W := mkw 0x00291c023298dc88 0x00148e01194c6e44 0x7f7b1c667f99ff99 0xbfbd8e333fccffcc

def z899 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x2b03e0607fe1ffe1 0x1581f0303ff0fff0

def z900 : W := mkw 0x287d1e26249c9118 0x943e8f13124e488c 0x10781c0600180018 0x883c0e03000c000c

def z901 : W := mkw 0x28391ea6249a9118 0x941c8f53124d488c 0x10781f8600180018 0x883c0fc3000c000c

def z902 : W := mkw 0x8e2bdb0aedd40354 0x4715ed8576ea01aa 0x8a03ff807ffe07ff 0xc501ffc03fff03ff

def z903 : W := mkw 0x57c6e05949652264 0x2be3702ca4b29132 0x0080e01800600060 0x0040700c00300030

def z904 : W := mkw 0x00006488502bc420 0x000032442815e210 0xde84ff9ff07fc47e 0xef427fcff83fe23f

def z905 : W := mkw 0x9df7db7fec00000a 0x4efbedbff6000005 0xfdfffffffe00001e 0xfeffffffff00000f

def z906 : W := mkw 0x20391da6a49a911a 0x101c8ed3524d488d 0x10781f8600180018 0x883c0fc3000c000c

def z907 : W := mkw 0x9ff7db7fed440244 0x4ffbedbff6a20122 0x7dfffffffe000000 0x3effffffff000000

def z908 : W := mkw 0x125c007500940354 0x092e003a804a01aa 0xd6fc007f807e07ff 0xeb7e003fc03f03ff

def z909 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0x9484ff9ff07e047e 0xca427fcff83f023f

def z910 : W := mkw 0x0de7db5ae8000000 0x06f3edad74000000 0x7dfffffffe000000 0x3effffffff000000

def z911 : W := mkw 0x4782e1d8db636ee2 0x23c170ec6db1b771 0x6f83e3f87fe1ffe1 0x37c1f1fc3ff0fff0

def z912 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x7f87e0787fffffe1 0x3fc3f03c3ffffff0

def z913 : W := mkw 0x20391c2624989118 0x101c8e13124c488c 0xd6fc1c1f807e047e 0xeb7e0e0fc03f023f

def z914 : W := mkw 0x058280501a004c80 0x02c140280d002640 0x6f0300607f81ff81 0x378180303fc0ffc0

def z915 : W := mkw 0x20391ca6249e9118 0x901c8e53124f488c 0x10781c06001e0018 0x883c0e03000f000c

def z916 : W := mkw 0x8c33db2eec000000 0x4619ed9776000000 0x187bff867e000000 0x0c3dffc33f000000

def z917 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x7fffffe67f99ff99 0xbffffff33fccffcc

def z918 : W := mkw 0x4782a0501b616ee0 0x23c150280db0b770 0x6f0300607fe1ffe1 0x378180303ff0fff0

def z919 : W := mkw 0x0382a05013616ec0 0x01c1502809b0b760 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z920 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0xffff007ffffe07ff 0xffff803fffff03ff

def z921 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x7fffff9f81fff800 0x3fffffcfc0fffc00

def z922 : W := mkw 0x1befb6d101ffb244 0x8df7db6880ffd922 0xffffff9f81fffc7e 0xffffffcfc0fffe3f

def z923 : W := mkw 0x4782e0d85b676ee0 0xa3c1706c2db3b770 0x6f83e0787fe7ffe1 0x37c1f03c3ff3fff0

def z924 : W := mkw 0xa410492efe004d98 0x520824977f0026cc 0x040000667e000799 0x820000333f0003cc

def z925 : W := mkw 0x8defb6800dffb000 0xc6f7db4006ffd800 0x7bffff800ffff800 0x3dffffc007fffc00

def z926 : W := mkw 0x0000400852004ca0 0x0000200429002650 0x6f0300787f81ffe1 0x3781803c3fc0fff0

def z927 : W := mkw 0x1befb6d101ffb354 0x8df7db6880ffd9aa 0xfbffff9981ffffff 0xfdffffccc0ffffff

def z928 : W := mkw 0x15d6c97fe8000000 0x0aeb64bff4000000 0x7dfffffffe000000 0x3effffffff000000

def z929 : W := mkw 0xdfc6e3d9db636ee2 0x6fe371ecedb1b771 0xef87e3f9ffe7ffe7 0x77c3f1fcfff3fff3

def z930 : W := mkw 0x00391c2624989110 0x001c8e13124c4888 0x7f7b1c667f99ff99 0xbfbd8e333fccffcc

def z931 : W := mkw 0x478040585b404ee0 0x23c0202c2da02770 0x6f8300787fe1ffe1 0x37c1803c3ff0fff0

def z932 : W := mkw 0x0010002412004c80 0x0008001209002640 0x7f7b00667f81ff81 0x3fbd80333fc0ffc0

def z933 : W := mkw 0x0031182624000000 0x00188c1312000000 0x7dffffe67e000000 0x3efffff33f000000

def z934 : W := mkw 0x2008248013fffdba 0x9004124009fffedd 0x8200000001ffffff 0xc100000000ffffff

def z935 : W := mkw 0x4582e0085b616ca0 0x22c170042db0b650 0x6f83e0607fe1ff81 0x37c1f0303ff0ffc0

def z936 : W := mkw 0x20391c2624989118 0x101c8e13124c488c 0x56781c0600180418 0xab3c0e03000c020c

def z937 : W := mkw 0xb87d1fa7a49a911a 0x5c3e8fd3d24d488d 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z938 : W := mkw 0x47c6e0585b616ee0 0x23e3702c2db0b770 0x7fffe0787fe1ffe1 0x3ffff03c3ff0fff0

def z939 : W := mkw 0x20006d8af62bccaa 0x100036c57b15e655 0xde84ff9ffe7fc47e 0xef427fcfff3fe23f

def z940 : W := mkw 0x0200005012004ec0 0x0100002809002760 0x6f0300787f81ffe1 0x3781803c3fc0fff0

def z941 : W := mkw 0xdff7db7fec000260 0x6ffbedbff6000130 0x7dfffffffe000060 0x3effffffff000030

def z942 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x7ffffffffe600460 0x3fffffffff300230

def z943 : W := mkw 0x01cc248001ffb000 0x80e6124000ffd800 0x7bfcff8001fff800 0x3dfe7fc000fffc00

def z944 : W := mkw 0x20006d8af22bdcaa 0x100036c57915ee55 0xde84ff9ff07ffc7e 0xef427fcff83ffe3f

def z945 : W := mkw 0x8c33db2eec000000 0x4619ed9776000000 0x297bffe07e000000 0x14bdfff03f000000

def z946 : W := mkw 0x4fc6e2585b616ee0 0x27e3712c2db0b770 0x6f87e3f87fe1ffe1 0x37c3f1fc3ff0fff0

def z947 : W := mkw 0x086fb68000bfb000 0x8437db40005fd800 0x7b7fff80019ff800 0x3dbfffc000cffc00

def z948 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0xffff007f81ffffff 0xffff803fc0ffffff

def z949 : W := mkw 0x17de807509d40354 0x0bef403a84ea01aa 0xf7ff007f8ffe07ff 0xfbff803fc7ff03ff

def z950 : W := mkw 0x9df7db7fec000110 0x4efbedbff6000088 0x7dfffffffe000799 0xbeffffffff0003cc

def z951 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0xfdfffffffe660066 0x7effffffff330033

def z952 : W := mkw 0x9df7db7fed442000 0xcefbedbff6a21000 0x7dfffffffe000000 0x3effffffff000000

def z953 : W := mkw 0x09e7b680016fb000 0x84f3db4000b7d800 0x79ffff800067f800 0x3cffffc00033fc00

def z954 : W := mkw 0x4782e0d85b636ee0 0x23c1706c2db1b770 0x6f87e3f87fe7ffe1 0x37c3f1fc3ff3fff0

def z955 : W := mkw 0x13d4007500000354 0x09ea003a800001aa 0xf7fc007f807e07ff 0xfbfe003fc03f03ff

def z956 : W := mkw 0x47c6e0585b656ee0 0x23e3702c2db2b770 0x6f87e0787fe7ffe1 0x37c3f03c3ff3fff0

def z957 : W := mkw 0x4782c0585a004ee0 0x23c1602c2d002770 0x6f83e0787f81ffe1 0x37c1f03c3fc0fff0

def z958 : W := mkw 0x0defb6d009ffb000 0x86f7db6804ffd800 0x7bffffe00ffff800 0x3dfffff007fffc00

def z959 : W := mkw 0x0002a00012216c80 0x000150000910b640 0x6f03e0607f81ff81 0x3781f0303fc0ffc0

def z960 : W := mkw 0x4fc6e25849612260 0x27e3712c24b09130 0x0084e39800600060 0x004271cc00300030

def z961 : W := mkw 0x9df7db7fec040004 0x4efbedbff6020002 0xfdfffffffe060006 0x7effffffff030003

def z962 : W := mkw 0x0823b680002bb000 0x8411db400015d800 0x797bff800001f800 0x3cbdffc00000fc00

def z963 : W := mkw 0x202914001298dd98 0x10148a00094c6ecc 0x7f7b1c607f99ff99 0xbfbd8e303fccffcc

def z964 : W := mkw 0x20311c263608dc88 0x10188e131b046e44 0x7f7b1c667f81ff81 0x3fbd8e333fc0ffc0

def z965 : W := mkw 0x086d368000bf9000 0x84369b40005fc800 0x7bffff8001fff800 0x3dffffc000fffc00

def z966 : W := mkw 0x0867b680002bb000 0x8433db400015d800 0x187fff800001f800 0x0c3fffc00000fc00

def z967 : W := mkw 0x20391c2624989118 0x101c8e13124c488c 0x00781c0000000000 0x003c0e0000000000

def z968 : W := mkw 0x478280501b406ec0 0x23c140280da03760 0x6f8300787fe1ffe1 0x37c1803c3ff0fff0

def z969 : W := mkw 0x1befb6d101ffb244 0x8df7db6880ffd922 0x7bffff8001fff800 0x3dffffc000fffc00

def z970 : W := mkw 0x44006d8afa2bccaa 0x220036c57d15e655 0xde84ff9ffe7fc47e 0xef427fcfff3fe23f

def z971 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0xef83e07fffe1ffff 0xf7c1f03ffff0ffff

def z972 : W := mkw 0x47c6e05849652260 0x23e3702c24b29130 0x0084e01800660060 0x0042700c00330030

def z973 : W := mkw 0x4200000012004ee0 0x2100000009002770 0x6f0300607f81ffe1 0x378180303fc0fff0

def z974 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x7d7b1c667f81fb81 0x3ebd8e333fc0fdc0

def z975 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x6b83e0607fe1fb81 0x35c1f0303ff0fdc0

def z976 : W := mkw 0x0582e0585a214ca0 0x02c1702c2d10a650 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z977 : W := mkw 0xb410497ffe004c88 0x5a0824bfff002644 0x0400007ffe000000 0x0200003fff000000

def z978 : W := mkw 0x0200000013404ec0 0x0100000009a02760 0x6f0300607fe1ffe1 0x378180303ff0fff0

def z979 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x7fffffffff800781 0x3fffffffffc003c0

def z980 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x270300787fe1ffe1 0x1381803c3ff0fff0

def z981 : W := mkw 0x00006d8ae02b802a 0x000036c57015c015 0xdc84ff9ff07e007e 0xee427fcff83f003f

def z982 : W := mkw 0x0000200012214c80 0x000010000910a640 0x6f83e0607fe1ff81 0x37c1f0303ff0ffc0

def z983 : W := mkw 0x9ff7db7fed440244 0x4ffbedbff6a20122 0xfffffffffe7e047e 0xffffffffff3f023f

def z984 : W := mkw 0x478280501b406ec0 0x23c140280da03760 0x290300607f81fb81 0x148180303fc0fdc0

def z985 : W := mkw 0x09e7b28001672000 0x84f3d94000b39000 0x7bffff8001e7f800 0x3dffffc000f3fc00

def z986 : W := mkw 0x0df7da7e6c000000 0x06fbed3f36000000 0x7dfffffe7e000000 0x3effffff3f000000

def z987 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0x94fc007f807e07ff 0xca7e003fc03f03ff

def z988 : W := mkw 0xbdf7db7fec000118 0x5efbedbff600008c 0x7dfffffffe000018 0xbeffffffff00000c

def z989 : W := mkw 0x33fd1c7725dc935c 0x19fe8e3b92ee49ae 0x90fc1c1f807e007e 0xc87e0e0fc03f003f

def z990 : W := mkw 0x20391d26b698dd9a 0x101c8e935b4c6ecd 0xff7b1c67ff99ff9f 0xffbd8e33ffccffcf

def z991 : W := mkw 0x2208248013ffffdc 0x9104124009ffffee 0x8200000001ffffff 0xc100000000ffffff

def z992 : W := mkw 0x307d1c27249c911c 0x183e8e13924e488e 0x10781c0600180018 0x883c0e03000c000c

def z993 : W := mkw 0x20391d26b698dd98 0x101c8e935b4c6ecc 0x7f7f1fe7ff99ff99 0xbfbf8ff3ffccffcc

def z994 : W := mkw 0x00006d8af02bc42a 0x000036c57815e215 0xff87fffffe7fc47e 0xffc3ffffff3fe23f

def z995 : W := mkw 0x4602e0585a216ee0 0x2301702c2d10b770 0x6f03e0787f81ffe1 0x3781f03c3fc0fff0

def z996 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x7b7b1c607f99fb81 0x3dbd8e303fccfdc0

def z997 : W := mkw 0x5fff92750bd43bd4 0xafffc93a85ea1dea 0x217b00600f803b81 0x10bd803007c01dc0

def z998 : W := mkw 0x201804241298dd98 0x100c0212094c6ecc 0x7f7b00667f99ff99 0xbfbd80333fccffcc

def z999 : W := mkw 0x40006d8af22becaa 0x200036c57915f655 0xde84ff9ff07ffc7e 0xef427fcff83ffe3f

def z1000 : W := mkw 0x0380005013404ec0 0x01c0002809a02760 0x6f0300607f81ff81 0x378180303fc0ffc0

def z1001 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0xff7b1c7fff99ffff 0xffbd8e3fffccffff

def z1002 : W := mkw 0x0000200012214ca0 0x000010000910a650 0x6f0300607fe1ffe1 0x378180303ff0fff0

def z1003 : W := mkw 0x4208248013ffeffe 0x2104124009fff7ff 0x8200000001ffffff 0xc100000000ffffff

def z1004 : W := mkw 0x0582e0585b616c80 0x02c1702c2db0b640 0x6f83e0787fe1ff81 0x37c1f03c3ff0ffc0

def z1005 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x7d7bffe67e000000 0x3ebdfff33f000000

def z1006 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x6bfbff8001e1f800 0x35fdffc000f0fc00

def z1007 : W := mkw 0xbfff92750fd41bd4 0x5fffc93a87ea0dea 0x217b00600f803b81 0x10bd803007c01dc0

def z1008 : W := mkw 0x9df7db7fec000114 0x4efbedbff600008a 0xfdfffffffe00001e 0xfeffffffff00000f

def z1009 : W := mkw 0x1bde827501d42354 0x8def413a80ea11aa 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z1010 : W := mkw 0x987d1fa7a49e9114 0xcc3e8fd3d24f488a 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z1011 : W := mkw 0x9ff7db7fed400240 0x4ffbedbff6a00120 0x7dffffffff800381 0x3effffffffc001c0

def z1012 : W := mkw 0x20391c2624989118 0x101c8e13124c488c 0x907c1c07801e001e 0xc83e0e03c00f000f

def z1013 : W := mkw 0x040040585a004c80 0x0200202c2d002640 0x6f0300787f81ff81 0x3781803c3fc0ffc0

def z1014 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x2d7bfffffe000000 0x16bdffffff000000

def z1015 : W := mkw 0x28391ea6369add98 0x941c8f531b4d6ecc 0x7f7b1fe67f99ff99 0xbfbd8ff33fccffcc

def z1016 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0xff7f1c67ff9fff9f 0xffbf8e33ffcfffcf

def z1017 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x2b7bff8001fff800 0x15bdffc000fffc00

def z1018 : W := mkw 0x00004d0af008c408 0x0000268578046204 0xde84ff9ff07fc47e 0xef427fcff83fe23f

def z1019 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x6dfbfff87e000000 0x36fdfffc3f000000

def z1020 : W := mkw 0x4200600853616ee0 0x2100300429b0b770 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z1021 : W := mkw 0x4000200012216ca0 0x200010000910b650 0x6f0300607f81ff81 0x378180303fc0ffc0

def z1022 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x12fcff8001fff800 0x097e7fc000fffc00

def z1023 : W := mkw 0x9df79a772c000000 0x4efbcd3b96000000 0x7dffffe67e000000 0x3efffff33f000000

def z1024 : W := mkw 0x086fb68000bfb000 0x8437db40005fd800 0x5affff80007ff800 0x2d7fffc0003ffc00

def z1025 : W := mkw 0x0218002401d40354 0x010c001200ea01aa 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z1026 : W := mkw 0x00006588c02b8022 0x000032c46015c011 0xde84ff9f807fc47e 0xef427fcfc03fe23f

def z1027 : W := mkw 0x0000200013616c80 0x0000100009b0b640 0x6f0300607fe1ff81 0x378180303ff0ffc0

def z1028 : W := mkw 0xa8391f26b698dd98 0x541c8f935b4c6ecc 0x7f7b1fe67f99ff99 0xbfbd8ff33fccffcc

def z1029 : W := mkw 0x57c6e0595b656ee4 0x2be3702cadb2b772 0xff87e07fffffffff 0xffc3f03fffffffff

def z1030 : W := mkw 0x0031102416004c80 0x001888120b002640 0x6f7b00607f81ff81 0x37bd80303fc0ffc0

def z1031 : W := mkw 0x6208248013fffff8 0xb104124009fffffc 0x0200000001fffff9 0x8100000000fffffc

def z1032 : W := mkw 0x8df7db2eec000000 0x46fbed9776000000 0x7dffffe67e000000 0x3efffff33f000000

def z1033 : W := mkw 0x287d1e2624989118 0x143e8f13124c488c 0x107c1f8600180018 0x883e0fc3000c000c

def z1034 : W := mkw 0xb610497ffe004fdc 0x5b0824bfff0027ee 0x8400007ffe0007ff 0xc200003fff0003ff

def z1035 : W := mkw 0xdfff92750fd42bd4 0x6fffc93a87ea15ea 0x217b00600f803b81 0x10bd803007c01dc0

def z1036 : W := mkw 0x20391c263698ddba 0x101c8e131b4c6edd 0xff7b1c667f99ffff 0xffbd8e333fccffff

def z1037 : W := mkw 0x5782e0595b616ee4 0x2bc1702cadb0b772 0xef83e079ffe1ffe7 0x77c1f03cfff0fff3

def z1038 : W := mkw 0x9df7db7fec003000 0xcefbedbff6001800 0x7dfffffffe003800 0x3effffffff001c00

def z1039 : W := mkw 0x4402e0085a216ca0 0x220170042d10b650 0x2903e0607f81fb81 0x1481f0303fc0fdc0

def z1040 : W := mkw 0xdfc6e3d9c9672260 0xefe371ece4b39130 0x0084e39980660060 0x004271ccc0330030

def z1041 : W := mkw 0x0029348001ffb000 0x80149a4000ffd800 0x7bffff8001fff800 0x3dffffc000fffc00

def z1042 : W := mkw 0x9fde827509d40354 0x4fef413a84ea01aa 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z1043 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0xff7b1c667fffffff 0xffbd8e333fffffff

def z1044 : W := mkw 0x20391ca6249a9118 0x101c8e53124d488c 0x107c1f86001e0018 0x883e0fc3000f000c

def z1045 : W := mkw 0x207d1c26249c9118 0x103e8e13124e488c 0x107c1c06001e0018 0x883e0e03000f000c

def z1046 : W := mkw 0x8c23db0aec000000 0x4611ed8576000000 0x797bff807e000000 0x3cbdffc03f000000

def z1047 : W := mkw 0x0380605853614ee0 0x01c0302c29b0a770 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z1048 : W := mkw 0x8db3db7eec000000 0x46d9edbf76000000 0x7dfbfffe7e000000 0x3efdffff3f000000

def z1049 : W := mkw 0x01ed348001ff9000 0x00f69a4000ffc800 0x7bffff8001fff800 0x3dffffc000fffc00

def z1050 : W := mkw 0x09efb68001ffb022 0x84f7db4000ffd811 0xfbffff8001fff866 0x7dffffc000fffc33

def z1051 : W := mkw 0x2031182636004d98 0x10188c131b0026cc 0x7f7b1c667f81ff99 0xbfbd8e333fc0ffcc

def z1052 : W := mkw 0x20391d26a498911a 0x101c8e93524c488d 0x90781c078018001e 0xc83c0e03c00c000f

def z1053 : W := mkw 0x19f79a7724000000 0x0cfbcd3b92000000 0x7dfffffffe000000 0x3effffffff000000

def z1054 : W := mkw 0x8de7db0aec000000 0x46f3ed8576000000 0x7dffff9ffe000000 0x3effffcfff000000

def z1055 : W := mkw 0x0029348000bb9000 0x00149a40005dc800 0x7b7bff800199f800 0x3dbdffc000ccfc00

def z1056 : W := mkw 0x4782e1d8db636ee2 0x23c170ec6db1b771 0xff87e3ffffffffff 0xffc3f1ffffffffff

def z1057 : W := mkw 0x13dc007501d43354 0x89ee003a80ea19aa 0xf7fc007f81fe3fff 0xfbfe003fc0ff1fff

def z1058 : W := mkw 0x20291c023698dc88 0x10148e011b4c6e44 0x7f7b1c607f99ff81 0x3fbd8e303fccffc0

def z1059 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0x7fffffffff81f800 0x3fffffffffc0fc00

def z1060 : W := mkw 0x00006d8af22bccaa 0x000036c57915e655 0xde84fffffe7fc7ff 0xef427fffff3fe3ff

def z1061 : W := mkw 0x4782e158db616ee2 0x23c170ac6db0b771 0xef83e079ffe1ffe7 0x77c1f03cfff0fff3

def z1062 : W := mkw 0x13dc007501d40354 0x09ee003a80ea01aa 0xa778007f81fe07ff 0xd3bc003fc0ff03ff

def z1063 : W := mkw 0x460060585a214ee0 0x2300302c2d10a770 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z1064 : W := mkw 0xdfc6e25949612260 0x6fe3712ca4b09130 0x0080e01800600060 0x0040700c00300030

def z1065 : W := mkw 0x0000000012004c80 0x0000000009002640 0x6f8300787fe1ffe1 0x37c1803c3ff0fff0

def z1066 : W := mkw 0x8c67db0aec000000 0x4633ed8576000000 0x187fff807e000000 0x0c3fffc03f000000

def z1067 : W := mkw 0x0befb6d001ffb354 0x85f7db6800ffd9aa 0xfffffff801ffffff 0xfffffffc00ffffff

def z1068 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x2d7b1c667f81ff99 0x96bd8e333fc0ffcc

def z1069 : W := mkw 0x09e7b680002bb000 0x84f3db400015d800 0x7bffff80007ff800 0x3dffffc0003ffc00

def z1070 : W := mkw 0x00006188d2234ca2 0x000030c46911a651 0xef87e3f9ffe7ffe7 0x77c3f1fcfff3fff3

def z1071 : W := mkw 0x00002480102bc42a 0x000012400815e215 0xde84ff9f807fc47e 0xef427fcfc03fe23f

def z1072 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x7fff1c7fff99ff99 0xbfff8e3fffccffcc

def z1073 : W := mkw 0x09efb60001f9b000 0x04f7db0000fcd800 0x7bffff8001f9f800 0x3dffffc000fcfc00

def z1074 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x79ffff800181f800 0x3cffffc000c0fc00

def z1075 : W := mkw 0x1218007501d40354 0x090c003a80ea01aa 0xf778007f81fe07ff 0xfbbc003fc0ff03ff

def z1076 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x2d03e0787f81ffe1 0x1681f03c3fc0fff0

def z1077 : W := mkw 0x09ef960001dcb000 0x84f7cb0000ee5800 0x7bffff800199f800 0x3dffffc000ccfc00

def z1078 : W := mkw 0x57de807509d42354 0x2bef403a84ea11aa 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z1079 : W := mkw 0x09e79a0224000000 0x04f3cd0112000000 0x79ffff807e000000 0x3cffffc03f000000

def z1080 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x7fffffe07ffff800 0x3ffffff03ffffc00

def z1081 : W := mkw 0xb87d1e2724989118 0x5c3e8f13924c488c 0x10781c0600180018 0x883c0e03000c000c

def z1082 : W := mkw 0x01dc002401d40110 0x00ee001200ea0088 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z1083 : W := mkw 0x9431597fec000000 0x4a18acbff6000000 0x7dfffffffe000000 0x3effffffff000000

def z1084 : W := mkw 0x4382a00013616ee0 0x21c1500009b0b770 0x6f83e0607fe1ffe1 0x37c1f0303ff0fff0

def z1085 : W := mkw 0x05b3d97eec000000 0x02d9ecbf76000000 0x7dfffffffe000000 0x3effffffff000000

def z1086 : W := mkw 0x9ff7db7fed400240 0x4ffbedbff6a00120 0xfffffffffffe07ff 0xffffffffffff03ff

def z1087 : W := mkw 0x09efb68001ffb110 0x84f7db4000ffd888 0x7bffff8001ffff99 0xbdffffc000ffffcc

def z1088 : W := mkw 0xdfc6e359c9652264 0x6fe371ace4b29132 0x8084e39980660066 0x404271ccc0330033

def z1089 : W := mkw 0x9ff7db7fec000240 0x4ffbedbff6000120 0x7dfffffffe0007e1 0x3effffffff0003f0

def z1090 : W := mkw 0x0180005012004c80 0x00c0002809002640 0x6f8300787f81ff81 0x37c1803c3fc0ffc0

def z1091 : W := mkw 0x0000000012004c80 0x0000000009002640 0x290300607f81fb81 0x148180303fc0fdc0

def z1092 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0x397fff80019ff800 0x1cbfffc000cffc00

def z1093 : W := mkw 0x086fb68000bfb000 0x8437db40005fd800 0x087bff800001f800 0x043dffc00000fc00

def z1094 : W := mkw 0x09efb20001f52000 0x04f7d90000fa9000 0x7bffff8001fff800 0x3dffffc000fffc00

def z1095 : W := mkw 0x082b960000989000 0x0415cb00004c4800 0x7b7bff800199f800 0x3dbdffc000ccfc00

def z1096 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x2b7b1c607f99ff99 0x95bd8e303fccffcc

def z1097 : W := mkw 0x0000000012004c80 0x0000000009002640 0x7f0300667f99ff99 0xbf8180333fccffcc

def z1098 : W := mkw 0x203914241698dd98 0x101c8a120b4c6ecc 0x6f7b00607f99ff99 0xb7bd80303fccffcc

def z1099 : W := mkw 0x8de7db5aec000000 0x46f3edad76000000 0x7dfffff87e000000 0x3efffffc3f000000

def z1100 : W := mkw 0x0000698ae0230022 0x000034c570118011 0xde84ff9ff07e047e 0xef427fcff83f023f

def z1101 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x7ffb1c7e7ff9fff9 0xbffd8e3f3ffcfffc

def z1102 : W := mkw 0x0befb6d001ffb240 0x85f7db6800ffd920 0xffffffff81ffffff 0xffffffffc0ffffff

def z1103 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0xef87e079ffe7ffe7 0x77c3f03cfff3fff3

def z1104 : W := mkw 0x0befb6d001ffb240 0x85f7db6800ffd920 0x7bffffe001fffb81 0x3dfffff000fffdc0

def z1105 : W := mkw 0xb87d1f27a49c911c 0x5c3e8f93d24e488e 0x907c1f87801e001e 0xc83e0fc3c00f000f

def z1106 : W := mkw 0x4782e0585b616eea 0x23c1702c2db0b775 0xef83e0787fe1ffff 0xf7c1f03c3ff0ffff

def z1107 : W := mkw 0x00006d8ae02b8000 0x000036c57015c000 0xde84ff9ff07fc47e 0xef427fcff83fe23f

def z1108 : W := mkw 0x0018002412904d90 0x000c0012094826c8 0x6f7b00607f81ff81 0x37bd80303fc0ffc0

def z1109 : W := mkw 0x9df7db7fed440000 0x4efbedbff6a20000 0x7dfffffffe660000 0x3effffffff330000

def z1110 : W := mkw 0xb0391d27b698dd98 0x581c8e93db4c6ecc 0x7f7b1c67ff99ff99 0xbfbd8e33ffccffcc

def z1111 : W := mkw 0x2039182636905d98 0x101c8c131b482ecc 0x6f7b00667f81ff99 0xb7bd80333fc0ffcc

def z1112 : W := mkw 0x09efb68001ffb000 0x84f7db4000ffd800 0xfbffff8001fffc7e 0xfdffffc000fffe3f

def z1113 : W := mkw 0x20391c2626989990 0x101c8e13134c4cc8 0x7f7b1c667f99fb81 0x3fbd8e333fccfdc0

def z1114 : W := mkw 0x0befb68001ffb354 0x85f7db4000ffd9aa 0xffffff9f81ffffff 0xffffffcfc0ffffff

def z1115 : W := mkw 0x20391c26369cdd9c 0x101c8e131b4e6ece 0xff7b1c667f9fff9f 0xffbd8e333fcfffcf

def z1116 : W := mkw 0x440040085a004ca0 0x220020042d002650 0x6f0300607f81ff81 0x378180303fc0ffc0

def z1117 : W := mkw 0x4582e0585a216ca0 0x22c1702c2d10b650 0x6f83e0787f81ff81 0x37c1f03c3fc0ffc0

def z1118 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x7f87e07fffe1ffe1 0x3fc3f03ffff0fff0

def z1119 : W := mkw 0x0befb68001ffb354 0x85f7db4000ffd9aa 0x7bffff8001fffb81 0x3dffffc000fffdc0

def z1120 : W := mkw 0x20391c263698dd98 0x101c8e131b4c6ecc 0x7fff1c667fffff99 0xbfff8e333fffffcc

def z1121 : W := mkw 0x4fefb6d009ffb240 0xa7f7db6804ffd920 0x7bffff8001fff800 0x3dffffc000fffc00

def z1122 : W := mkw 0x0782c0585b404ec0 0x03c1602c2da02760 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z1123 : W := mkw 0x0000490af000442a 0x0000248578002215 0xde84ff9ff07e047e 0xef427fcff83f023f

def z1124 : W := mkw 0x125c007501d40354 0x092e003a80ea01aa 0x967c007f81fe07ff 0xcb3e003fc0ff03ff

def z1125 : W := mkw 0x03cc005001d40240 0x01e6002800ea0120 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z1126 : W := mkw 0x0befb68001ffb240 0x85f7db4000ffd920 0x7bffff8001ffffe1 0x3dffffc000fffff0

def z1127 : W := mkw 0x00006d8af22bccaa 0x000036c57915e655 0xde84ff9ff1ffffff 0xef427fcff8ffffff

def z1128 : W := mkw 0x9df7d27d4c000000 0x4efbe93ea6000000 0x7dfffff87e000000 0x3efffffc3f000000

def z1129 : W := mkw 0x0029100012905c80 0x0014880009482e40 0x6f7b00607f81ff81 0x37bd80303fc0ffc0

def z1130 : W := mkw 0x11dc007500900110 0x08ee003a80480088 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z1131 : W := mkw 0x20391ca6369edd98 0x901c8e531b4f6ecc 0x7f7b1c667f9fff99 0xbfbd8e333fcfffcc

def z1132 : W := mkw 0xbdffdf7fec989118 0x5effefbff64c488c 0x10fcff9f80180018 0x887e7fcfc00c000c

def z1133 : W := mkw 0x09e7b680002bb000 0x84f3db400015d800 0x297bff800001f800 0x14bdffc00000fc00

def z1134 : W := mkw 0x20391da6b69add9a 0x101c8ed35b4d6ecd 0x7f7b1fe67f99ff99 0xbfbd8ff33fccffcc

def z1135 : W := mkw 0x4402e0085a216ca0 0x220170042d10b650 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z1136 : W := mkw 0x4380205013616ee0 0x21c0102809b0b770 0x6f8300787fe1ffe1 0x37c1803c3ff0fff0

def z1137 : W := mkw 0x203914241698dd90 0x101c8a120b4c6ec8 0x7f7b1c607f99ff81 0x3fbd8e303fccffc0

def z1138 : W := mkw 0x1218007500900354 0x090c003a804801aa 0xf7fc007f81fe07ff 0xfbfe003fc0ff03ff

def z1139 : W := mkw 0x2010492ef6004dba 0x100824977b0026dd 0x040000667e000799 0x820000333f0003cc

def z1140 : W := mkw 0x4008248013fffca0 0xa004124009fffe50 0x0200000001fff800 0x0100000000fffc00

def z1141 : W := mkw 0x03cc000001d40354 0x01e6000000ea01aa 0xf7fc001f81fe07ff 0xfbfe000fc0ff03ff

def z1142 : W := mkw 0x0befb68001ffb244 0x85f7db4000ffd922 0xfbffff8001fff866 0x7dffffc000fffc33

def z1143 : W := mkw 0x30391c272498911c 0x181c8e13924c488e 0x90781c078018001e 0xc83c0e03c00c000f

def z1144 : W := mkw 0x00006d8ae02b802a 0x000036c57015c015 0xda84ff9f807fc07e 0xed427fcfc03fe03f

def z1145 : W := mkw 0x57c6e0595b616ee0 0x2be3702cadb0b770 0x6f87e079ffe1ffe1 0x37c3f03cfff0fff0

def z1146 : W := mkw 0x003914241298dd90 0x001c8a12094c6ec8 0x7f7b1c667f99ff99 0xbfbd8e333fccffcc

def z1147 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x6d83e0787f81fb81 0x36c1f03c3fc0fdc0

def z1148 : W := mkw 0x00002c82302bc408 0x000016411815e204 0xde84ff9ff07fc47e 0xef427fcff83fe23f

def z1149 : W := mkw 0x98755b2fe4000000 0x4c3aad97f2000000 0x7dfffffffe000000 0x3effffffff000000

def z1150 : W := mkw 0xd610497ffe004eea 0x6b0824bfff002775 0x8400007ffe0007ff 0xc200003fff0003ff

def z1151 : W := mkw 0x2008248012bbfd98 0x90041240095dfecc 0x020000000199ff99 0x8100000000ccffcc

def z1152 : W := mkw 0x4200000013406ec0 0x2100000009a03760 0x6f0300607f81ff81 0x378180303fc0ffc0

def z1153 : W := mkw 0x8de7db0aec000000 0x46f3ed8576000000 0x297bff807e000000 0x14bdffc03f000000

def z1154 : W := mkw 0x2039182636905d90 0x101c8c131b482ec8 0x7f7b1c667f81ff81 0x3fbd8e333fc0ffc0

def z1155 : W := mkw 0x0000600852214ca0 0x000030042910a650 0x6f03e0607f81ff81 0x3781f0303fc0ffc0

def z1156 : W := mkw 0x1bde827501d40354 0x0def413a80ea01aa 0xf7fce3ff81fe07ff 0xfbfe71ffc0ff03ff

def z1157 : W := mkw 0x1bff927501d40354 0x0dffc93a80ea01aa 0x217b006001800381 0x10bd803000c001c0

def z1158 : W := mkw 0x09efb68001ffb00a 0x84f7db4000ffd805 0xfbffff8001fff81e 0xfdffffc000fffc0f

def z1159 : W := mkw 0x9ff7db7fec000244 0x4ffbedbff6000122 0xfdfffffffe000066 0x7effffffff000033

def z1160 : W := mkw 0x0402c0085a004c80 0x020160042d002640 0x6f03e0607f81ff81 0x3781f0303fc0ffc0

def z1161 : W := mkw 0x0000000000000000 0x0000000000000000 0xde84ff9f807e047e 0xef427fcfc03f023f

def z1162 : W := mkw 0x57c6e05949612260 0x2be3702ca4b09130 0x0084e01980600060 0x0042700cc0300030

def z1163 : W := mkw 0xdfc6e3d9db676ee0 0xefe371ecedb3b770 0x6f87e3f9ffe7ffe1 0x37c3f1fcfff3fff0

def z1164 : W := mkw 0x00002d82a02b800a 0x000016c15015c005 0xde84ff9f807fc47e 0xef427fcfc03fe23f

def z1165 : W := mkw 0xdff7db7fed402240 0x6ffbedbff6a01120 0x7dfffffffe000000 0x3effffffff000000

def z1166 : W := mkw 0x5fc6e2d95b676ee4 0xafe3716cadb3b772 0xef87e3f9ffe7ffe7 0x77c3f1fcfff3fff3

def z1167 : W := mkw 0x9df7db7fec000000 0x4efbedbff6000000 0xfdfffffffe1e001e 0xfeffffffff0f000f

def z1168 : W := mkw 0x4782e158db616ee0 0x23c170ac6db0b770 0x6f87e3f9ffe1ffe1 0x37c3f1fcfff0fff0

def z1169 : W := mkw 0x0782e05849612240 0x03c1702c24b09120 0x6f83e0787fe1ffe1 0x37c1f03c3ff0fff0

def z1170 : W := mkw 0xb87d1fa7a49e9118 0xdc3e8fd3d24f488c 0x107c1f87801e0018 0x883e0fc3c00f000c

def z1171 : W := mkw 0x57c6e1d9db676ee6 0x2be370ecedb3b773 0xef87e3f9ffe7ffe7 0x77c3f1fcfff3fff3

def z1172 : W := mkw 0x20391ca6369add9a 0x101c8e531b4d6ecd 0xff7b1c667f9fff9f 0xffbd8e333fcfffcf

def z1173 : W := mkw 0xb0391d27a4989118 0x581c8e93d24c488c 0x10781c0780180018 0x883c0e03c00c000c

def z1174 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0x7f87fff87fe1ffe1 0x3fc3fffc3ff0fff0

def z1175 : W := mkw 0x4782e0585b616ee0 0x23c1702c2db0b770 0xef83e0787fffffff 0xf7c1f03c3fffffff

def z1176 : W := mkw 0x9df7db2fec000000 0x4efbed97f6000000 0x79ffff87fe000000 0x3cffffc3ff000000

def z1177 : W := mkw 0x9ff7db7fed440354 0x4ffbedbff6a201aa 0xfdfffffffe6607ff 0xfeffffffff3303ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z1,z2,z8,z4,z6]),(0,[z0,z1,z2,z9,z4,z10,z6]),(1,[z0,z1,z2,z3,z11,z6])],[(0,[z0,z1,z2,z3,z4,z12,z6]),(0,[z0,z13,z1,z2,z3,z4,z6]),(0,[z0,z14,z15,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z16,z4,z6]),(0,[z0,z17,z1,z2,z3,z4,z6]),(0,[z0,z18,z1,z2,z3,z4,z6]),(1,[z19,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z4,z6]),(0,[z0,z21,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z9,z4,z6]),(0,[z22,z0,z1,z2,z3,z4,z6])],[(0,[z23,z0,z1,z2,z20,z3,z6]),(0,[z0,z1,z24,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z25]),(0,[z0,z26,z1,z2,z3,z4,z6])],[(1,[z0,z1,z27,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z8,z6]),(0,[z0,z1,z2,z3,z4,z6,z28]),(0,[z1,z2,z29,z30,z3,z4,z6]),(0,[z31,z0,z1,z2,z32,z3,z6])],[(0,[z0,z1,z2,z3,z4,z33,z6]),(0,[z0,z1,z34,z2,z3,z4,z6]),(0,[z35,z36,z1,z2,z3,z4,z6]),(0,[z35,z1,z2,z3,z4,z37,z6]),(0,[z0,z1,z2,z3,z4,z38,z6]),(1,[z31,z0,z39,z1,z2,z6])],[(0,[z23,z0,z1,z2,z40,z4,z6]),(0,[z0,z1,z2,z27,z3,z4,z6]),(1,[z41,z1,z2,z3,z42,z6]),(0,[z43,z0,z1,z2,z3,z44,z6]),(0,[z0,z45,z1,z2,z3,z4,z6]),(0,[z46,z31,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z47,z20,z3,z6]),(0,[z0,z1,z2,z3,z4,z48,z6])],[(0,[z23,z0,z1,z2,z3,z4,z49]),(0,[z0,z50,z1,z2,z3,z4,z6]),(0,[z0,z1,z51,z2,z3,z4,z6]),(1,[z31,z0,z1,z2,z3,z6])],[(1,[z0,z52,z2,z3,z53,z6]),(0,[z0,z1,z2,z54,z3,z4,z6]),(0,[z0,z1,z55,z2,z3,z56,z6]),(0,[z0,z1,z2,z3,z57,z4,z6]),(0,[z31,z0,z58,z1,z2,z3,z6])]],
   [[(0,[z59,z0,z60,z2,z3,z4,z6]),(0,[z61,z0,z1,z2,z3,z4,z6])],[(0,[z62,z59,z1,z2,z3,z4,z6]),(0,[z23,z62,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z63,z4,z6]),(0,[z0,z1,z2,z3,z4,z64,z65]),(0,[z0,z1,z2,z3,z66,z4,z6]),(0,[z0,z67,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z68,z4,z6])],[(0,[z0,z1,z2,z3,z4,z69,z6]),(0,[z0,z1,z2,z3,z4,z70,z6]),(0,[z0,z71,z1,z2,z3,z4,z6])],[(0,[z41,z0,z1,z2,z20,z3,z6]),(0,[z0,z1,z72,z2,z3,z4,z73]),(0,[z0,z74,z1,z2,z3,z4,z6]),(0,[z0,z1,z75,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z76,z6]),(0,[z0,z1,z2,z3,z44,z4,z6]),(0,[z1,z2,z3,z4,z37,z6,z65]),(0,[z0,z1,z2,z3,z4,z77,z6]),(0,[z0,z39,z2,z78,z3,z4,z6]),(0,[z0,z67,z2,z3,z4,z79,z6]),(0,[z31,z0,z1,z2,z3,z79,z6]),(0,[z80,z0,z1,z2,z3,z4,z6])],[(0,[z0,z81,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z82,z4,z6]),(0,[z0,z39,z1,z2,z3,z83,z6]),(0,[z0,z1,z84,z2,z3,z4,z6]),(0,[z0,z85,z1,z2,z3,z4,z86])],[(0,[z0,z1,z2,z3,z4,z87,z6]),(0,[z0,z52,z2,z30,z3,z4,z6]),(0,[z0,z1,z2,z3,z88,z4,z6]),(0,[z0,z1,z89,z2,z3,z4,z64]),(0,[z1,z2,z3,z4,z6,z90,z91]),(1,[z0,z92,z2,z3,z4,z6])],[(0,[z0,z1,z2,z93,z3,z4,z6]),(0,[z0,z14,z52,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z94,z6])]],
   [[(0,[z0,z1,z2,z95,z3,z4,z6]),(0,[z0,z1,z2,z96,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z53,z4,z97,z6]),(0,[z0,z1,z2,z3,z4,z98,z6]),(0,[z0,z1,z2,z3,z99,z4,z6])],[(0,[z0,z1,z2,z3,z100,z4,z6])],[(0,[z0,z1,z101,z2,z3,z4,z6]),(0,[z0,z102,z1,z2,z3,z4,z6]),(1,[z31,z0,z103,z1,z2,z6]),(0,[z0,z1,z32,z3,z104,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z105]),(0,[z0,z71,z1,z2,z3,z4,z64])],[(0,[z106,z0,z1,z2,z3,z4,z6]),(0,[z36,z1,z2,z3,z4,z6,z65]),(0,[z0,z1,z2,z3,z107,z4,z6]),(0,[z0,z39,z1,z2,z78,z4,z6]),(0,[z0,z1,z3,z4,z64,z6,z91])],[(0,[z0,z108,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z109,z4,z6]),(0,[z0,z110,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z78,z20,z3,z6]),(0,[z0,z111,z1,z2,z3,z112,z6]),(0,[z0,z1,z2,z3,z4,z113,z6]),(0,[z0,z1,z2,z114,z3,z4,z6])],[(0,[z0,z1,z72,z2,z20,z3,z6]),(0,[z0,z115,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z116,z4,z6]),(0,[z0,z2,z3,z4,z6,z117,z118])],[(0,[z0,z103,z2,z30,z3,z4,z6]),(0,[z0,z67,z1,z2,z3,z97,z6]),(0,[z0,z15,z1,z2,z3,z119,z4])],[(0,[z120,z0,z1,z2,z3,z4,z6]),(0,[z31,z121,z0,z1,z2,z3,z6]),(0,[z43,z0,z1,z2,z3,z42,z6]),(0,[z0,z122,z1,z2,z3,z4,z91]),(0,[z0,z1,z2,z3,z4,z6,z123]),(0,[z0,z1,z2,z124,z3,z4,z6])]],
   [[(0,[z23,z60,z1,z2,z3,z4,z6]),(0,[z125,z0,z1,z2,z3,z4,z6])],[(0,[z126,z0,z1,z2,z3,z4,z6]),(0,[z60,z1,z127,z2,z3,z4,z6]),(0,[z128,z0,z1,z2,z3,z4,z6]),(0,[z31,z0,z81,z1,z2,z3,z6]),(0,[z31,z0,z1,z2,z3,z129,z6]),(0,[z0,z1,z2,z3,z4,z130,z6]),(0,[z0,z111,z1,z131,z3,z4,z6])],[(0,[z0,z15,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z132,z6]),(0,[z0,z133,z1,z2,z3,z4,z6]),(0,[z0,z1,z134,z2,z3,z4,z6])],[(0,[z0,z1,z135,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z136]),(0,[z0,z122,z1,z2,z20,z3,z6]),(0,[z31,z0,z1,z2,z3,z6,z137])],[(0,[z138,z0,z1,z2,z3,z4,z6]),(0,[z139,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z140,z6]),(0,[z0,z1,z141,z2,z3,z4,z6]),(0,[z0,z142,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z143,z3,z6])],[],[(1,[z0,z144,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z145,z6]),(0,[z0,z146,z1,z2,z3,z4,z6])],[(0,[z0,z147,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z148,z3,z4,z6]),(0,[z0,z39,z1,z2,z129,z4,z6]),(0,[z0,z1,z2,z3,z4,z64,z6]),(0,[z0,z1,z2,z149,z3,z4,z6]),(0,[z150,z31,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z151,z6])]],
   [[(0,[z0,z1,z152,z2,z3,z4,z6]),(0,[z0,z153,z1,z2,z3,z4,z6]),(0,[z0,z154,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z155,z4,z6]),(1,[z0,z1,z2,z3,z4,z73]),(0,[z0,z156,z1,z2,z3,z4,z6]),(1,[z31,z0,z157,z1,z2,z6])],[(0,[z0,z1,z2,z3,z4,z158,z6]),(0,[z0,z1,z2,z3,z4,z6,z159]),(0,[z0,z15,z1,z2,z3,z4,z79]),(0,[z0,z1,z2,z3,z4,z6,z160])],[(0,[z0,z1,z2,z3,z4,z161,z6]),(0,[z0,z1,z162,z2,z3,z4,z6]),(0,[z0,z1,z2,z30,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z73]),(0,[z0,z1,z2,z3,z4,z163,z6]),(0,[z0,z1,z55,z2,z3,z4,z6]),(0,[z0,z1,z55,z2,z9,z4,z6]),(0,[z0,z164,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z112,z6]),(0,[z0,z1,z2,z143,z3,z4,z137])],[(0,[z0,z165,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z166,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z167]),(0,[z0,z1,z2,z3,z4,z168,z6])],[(0,[z0,z1,z2,z169,z3,z4,z6]),(0,[z0,z1,z170,z2,z3,z4,z6]),(0,[z171,z0,z1,z2,z3,z4,z6]),(0,[z43,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z172,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z173,z6])],[(0,[z0,z92,z1,z2,z3,z4,z6])],[(0,[z171,z0,z1,z2,z3,z8,z6]),(0,[z35,z0,z1,z2,z3,z4,z37]),(0,[z0,z1,z174,z2,z3,z4,z6]),(0,[z0,z175,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z176,z6]),(0,[z0,z1,z177,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z178,z6]),(0,[z0,z1,z2,z3,z4,z6,z179]),(0,[z180,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z111,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z91]),(0,[z0,z1,z2,z3,z4,z6,z117])],[(0,[z0,z60,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z32,z8,z4,z6]),(1,[z0,z1,z2,z3,z181,z6]),(0,[z0,z1,z2,z3,z4,z37,z91]),(0,[z182,z0,z1,z2,z3,z4,z6]),(0,[z31,z0,z67,z1,z2,z3,z6]),(0,[z0,z183,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z184,z4,z97])],[(0,[z23,z1,z2,z3,z4,z37,z6]),(0,[z0,z1,z185,z2,z3,z4,z6]),(0,[z0,z1,z186,z2,z3,z4,z6]),(0,[z0,z111,z164,z2,z3,z4,z6]),(1,[z0,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z4,z187,z6])],[(0,[z188,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z189]),(1,[z0,z71,z1,z3,z4,z64]),(1,[z190,z1,z2,z3,z4,z6]),(0,[z0,z191,z1,z2,z3,z4,z6]),(0,[z0,z1,z192,z2,z3,z4,z6])],[(0,[z7,z0,z1,z2,z109,z4,z6]),(0,[z0,z1,z2,z3,z181,z4,z6]),(0,[z0,z1,z2,z3,z4,z193,z6]),(0,[z0,z2,z3,z53,z4,z79,z6]),(0,[z0,z122,z2,z3,z4,z79,z6]),(1,[z0,z164,z2,z3,z4,z6]),(0,[z194,z1,z2,z3,z4,z6,z91])],[(0,[z195,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z40,z4,z6]),(0,[z0,z1,z2,z3,z44,z112,z6]),(1,[z0,z15,z2,z3,z4,z160]),(0,[z0,z157,z1,z55,z3,z4,z6])],[(0,[z0,z1,z2,z3,z181,z8,z6]),(0,[z0,z1,z2,z196,z3,z4,z6]),(1,[z35,z1,z2,z3,z4,z37]),(0,[z0,z197,z1,z2,z3,z4,z6]),(0,[z0,z1,z198,z2,z3,z4,z6]),(0,[z0,z122,z85,z1,z2,z3,z4]),(0,[z0,z1,z131,z2,z3,z199,z6]),(0,[z31,z0,z1,z131,z2,z3,z6]),(0,[z0,z85,z1,z2,z3,z119,z6])],[(0,[z0,z200,z1,z2,z3,z4,z6]),(0,[z0,z201,z1,z2,z3,z4,z6]),(0,[z0,z1,z202,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z203,z4,z6])]],
   [[(0,[z7,z0,z1,z2,z20,z3,z6]),(0,[z121,z0,z1,z2,z109,z4,z6]),(0,[z204,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z205,z4,z6])],[(0,[z206,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z207,z6]),(0,[z0,z122,z1,z2,z3,z4,z64]),(0,[z0,z1,z2,z3,z4,z6,z208]),(0,[z209,z31,z0,z1,z2,z3,z6]),(0,[z0,z210,z1,z2,z3,z4,z6])],[(0,[z211,z0,z1,z2,z3,z4,z6]),(1,[z0,z2,z212,z3,z4,z6]),(0,[z0,z213,z1,z2,z3,z4,z6]),(0,[z0,z214,z1,z2,z3,z4,z6])],[(0,[z215,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z216,z97,z6]),(0,[z0,z1,z2,z3,z4,z6,z217]),(0,[z0,z218,z1,z2,z3,z4,z6])],[(0,[z121,z0,z1,z2,z20,z3,z6]),(0,[z0,z219,z1,z2,z3,z4,z6]),(0,[z0,z220,z1,z2,z20,z3,z6])],[(1,[z0,z221,z1,z2,z3,z6]),(0,[z31,z0,z1,z2,z3,z10,z6])],[(1,[z0,z222,z2,z3,z4,z6]),(0,[z0,z1,z2,z223,z3,z4,z6]),(0,[z0,z14,z1,z2,z3,z4,z6]),(0,[z31,z0,z71,z1,z2,z3,z6]),(0,[z0,z21,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z20,z20,z3,z6]),(0,[z0,z1,z224,z2,z3,z4,z6])],[(0,[z31,z0,z1,z162,z2,z3,z6]),(0,[z0,z1,z2,z20,z3,z42,z6]),(0,[z0,z1,z2,z3,z4,z225,z6]),(0,[z0,z1,z226,z2,z3,z4,z6]),(0,[z227,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z129,z6]),(0,[z31,z0,z122,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z104,z4,z6]),(0,[z46,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z228])]],
   [[(1,[z0,z1,z2,z3,z4,z6]),(0,[z229,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z230,z2,z3,z4,z6]),(0,[z0,z81,z1,z30,z3,z4,z6]),(0,[z0,z1,z2,z3,z231,z4,z6]),(0,[z0,z1,z232,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z90]),(0,[z233,z31,z0,z1,z2,z3,z6])],[(0,[z31,z0,z1,z55,z2,z4,z6])],[(0,[z0,z1,z2,z3,z40,z4,z6]),(0,[z0,z1,z2,z3,z234,z4,z6]),(1,[z0,z81,z30,z3,z4,z6]),(0,[z0,z52,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z53,z6]),(0,[z0,z1,z235,z2,z3,z4,z6])],[(0,[z0,z1,z2,z236,z3,z4,z6]),(0,[z0,z1,z2,z3,z237,z4,z6]),(0,[z0,z201,z2,z3,z8,z4,z6]),(0,[z31,z0,z1,z2,z8,z4,z6]),(0,[z0,z1,z2,z3,z4,z37,z6]),(0,[z0,z1,z2,z3,z119,z4,z86])],[(1,[z36,z1,z2,z3,z4,z65]),(0,[z0,z1,z2,z3,z132,z104,z6]),(1,[z0,z17,z2,z3,z4,z6]),(0,[z238,z0,z1,z2,z3,z4,z6])],[(0,[z0,z239,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z240,z3,z4,z6]),(0,[z0,z1,z2,z241,z3,z8,z4]),(0,[z0,z1,z242,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z243,z4,z6]),(0,[z0,z1,z244,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z245,z4,z6]),(0,[z0,z1,z2,z3,z4,z246,z6])],[(0,[z31,z195,z0,z1,z2,z3,z6]),(0,[z31,z0,z1,z2,z3,z3,z6]),(0,[z0,z1,z2,z3,z247,z4,z6]),(0,[z0,z1,z2,z3,z4,z248,z6])],[(0,[z0,z249,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z250]),(0,[z0,z1,z2,z3,z251,z4,z6]),(0,[z0,z1,z2,z3,z4,z252,z6])]],
   [[(0,[z0,z1,z2,z253,z3,z4,z6]),(0,[z0,z254,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z255])],[(0,[z256,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z257,z6]),(0,[z0,z1,z2,z4,z258,z112,z6])],[(0,[z0,z1,z2,z3,z259,z4,z6]),(1,[z0,z1,z2,z3,z155,z6]),(0,[z0,z260,z1,z2,z3,z4,z6]),(0,[z0,z81,z1,z2,z20,z3,z6]),(0,[z0,z220,z1,z2,z3,z4,z6]),(1,[z0,z261,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z262,z6]),(0,[z0,z263,z1,z2,z3,z4,z6])],[(0,[z0,z103,z39,z2,z3,z4,z6]),(0,[z0,z264,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z265,z6]),(0,[z31,z0,z1,z2,z266,z3,z6])],[(0,[z0,z1,z2,z93,z20,z3,z6]),(0,[z267,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z241,z3,z4,z6]),(0,[z0,z1,z2,z3,z268,z4,z6]),(0,[z31,z0,z103,z1,z2,z3,z6]),(0,[z0,z1,z2,z143,z3,z4,z113])],[(0,[z195,z0,z1,z93,z3,z4,z6]),(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z269,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z270,z4,z6]),(0,[z36,z0,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z4,z271,z6]),(0,[z0,z1,z2,z3,z272,z4,z6]),(0,[z0,z111,z1,z3,z4,z112,z6]),(0,[z0,z1,z2,z3,z9,z4,z6]),(0,[z0,z1,z2,z143,z4,z113,z6]),(0,[z0,z273,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z274,z3,z4,z6])],[(0,[z275,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z55,z32,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z118])],[(0,[z0,z276,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z277,z6]),(0,[z0,z1,z2,z3,z4,z6,z278]),(0,[z0,z85,z1,z2,z3,z6,z118])]],
   [[(0,[z35,z0,z58,z1,z2,z3,z4]),(0,[z279,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z280,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z281,z137]),(1,[z0,z1,z2,z4,z6,z282])],[(0,[z0,z1,z2,z3,z4,z6,z283]),(0,[z284,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z285,z4,z6]),(0,[z286,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z287,z4,z6]),(0,[z0,z58,z1,z2,z4,z6,z137])],[(0,[z0,z1,z288,z2,z3,z4,z6])],[(0,[z31,z59,z0,z1,z2,z3,z6]),(1,[z0,z1,z2,z289,z4,z6]),(1,[z0,z39,z2,z78,z4,z6]),(0,[z0,z15,z1,z2,z3,z4,z91]),(0,[z0,z1,z290,z2,z3,z4,z6])],[(0,[z121,z0,z1,z2,z3,z155,z6]),(0,[z0,z291,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z3,z4,z6,z292]),(0,[z0,z1,z2,z3,z4,z293,z6]),(0,[z0,z71,z1,z89,z3,z4,z6])],[(0,[z0,z1,z2,z3,z294,z4,z6]),(0,[z0,z1,z2,z3,z295,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z296])],[(1,[z297,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z298,z3,z4,z6]),(0,[z0,z299,z1,z2,z3,z4,z6]),(0,[z0,z1,z300,z2,z3,z4,z6]),(0,[z0,z301,z1,z2,z3,z4,z6])],[(1,[z59,z60,z2,z3,z4,z6]),(0,[z0,z1,z2,z289,z3,z4,z6]),(0,[z0,z15,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z20,z3,z86,z6])]],
   [[(0,[z0,z103,z15,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z56,z6]),(0,[z0,z1,z2,z302,z3,z4,z6]),(0,[z0,z71,z303,z2,z3,z4,z6])],[(0,[z304,z0,z1,z2,z3,z4,z6]),(0,[z150,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z97,z6]),(0,[z138,z0,z1,z2,z20,z3,z6]),(0,[z0,z1,z305,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z306]),(0,[z0,z1,z2,z3,z4,z307,z6]),(0,[z0,z1,z2,z3,z270,z4,z6]),(0,[z43,z1,z2,z3,z44,z4,z6]),(0,[z0,z308,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z29,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z309,z6]),(1,[z0,z1,z2,z3,z6,z281])],[(0,[z0,z1,z310,z2,z3,z4,z6]),(0,[z7,z0,z1,z2,z8,z4,z6]),(0,[z0,z1,z2,z3,z311,z4,z6]),(0,[z0,z122,z1,z2,z3,z4,z160])],[(0,[z62,z1,z127,z2,z3,z4,z6]),(0,[z312,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z313,z6]),(0,[z36,z1,z162,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z42,z112,z6]),(0,[z31,z0,z1,z2,z3,z64,z6]),(1,[z31,z0,z1,z2,z113,z6]),(0,[z0,z1,z2,z20,z3,z314,z6])],[(0,[z0,z315,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z316,z6]),(0,[z0,z1,z317,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z318,z4,z6]),(0,[z0,z1,z319,z2,z3,z4,z6]),(0,[z0,z320,z1,z2,z3,z4,z6]),(0,[z0,z1,z321,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z282])],[(0,[z0,z322,z1,z2,z3,z4,z6])],[(0,[z0,z1,z162,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z323,z4,z6]),(0,[z0,z1,z2,z30,z20,z3,z6]),(0,[z0,z103,z2,z3,z129,z4,z6]),(0,[z0,z1,z55,z2,z104,z4,z6]),(0,[z0,z1,z55,z2,z20,z3,z6]),(0,[z0,z1,z2,z9,z4,z113,z6])]],
   [[(0,[z23,z195,z1,z2,z3,z4,z6]),(1,[z31,z0,z1,z2,z109,z6]),(0,[z0,z324,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z119,z86])],[(0,[z0,z1,z2,z3,z325,z4,z6]),(0,[z43,z0,z1,z2,z20,z3,z6]),(0,[z31,z0,z1,z2,z3,z6,z65]),(0,[z0,z326,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z327,z6]),(0,[z0,z1,z2,z3,z4,z6,z328]),(1,[z0,z1,z2,z3,z184,z4]),(0,[z329,z0,z1,z2,z3,z4,z6])],[(0,[z330,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z64,z37]),(0,[z0,z331,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z4,z10,z6])],[(0,[z195,z0,z1,z162,z3,z4,z6]),(0,[z31,z0,z1,z321,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z332,z6])],[(0,[z35,z0,z1,z2,z143,z3,z4]),(0,[z31,z0,z1,z2,z3,z6,z91]),(0,[z0,z1,z2,z3,z4,z333,z6]),(0,[z0,z334,z1,z2,z3,z4,z6])],[(0,[z0,z60,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z4,z42,z6]),(0,[z0,z1,z2,z3,z4,z335,z6]),(0,[z0,z1,z2,z336,z3,z4,z6]),(0,[z0,z1,z2,z3,z337,z4,z6])],[(0,[z0,z1,z2,z3,z338,z4,z6])]],
   [[(0,[z0,z14,z2,z3,z4,z97,z6]),(0,[z0,z1,z2,z339,z3,z4,z6])],[(0,[z0,z1,z2,z340,z3,z4,z6]),(0,[z0,z14,z1,z30,z3,z4,z6]),(0,[z0,z1,z341,z2,z3,z129,z4]),(0,[z0,z1,z2,z3,z4,z342,z6]),(0,[z0,z1,z343,z2,z3,z4,z6])],[(0,[z195,z0,z1,z2,z20,z3,z6]),(0,[z0,z2,z212,z3,z8,z4,z6]),(0,[z31,z0,z39,z1,z2,z4,z6]),(0,[z0,z1,z2,z344,z3,z4,z6]),(0,[z0,z345,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z346,z6]),(0,[z0,z1,z2,z3,z129,z4,z6]),(0,[z0,z1,z2,z347,z3,z4,z6]),(0,[z348,z0,z1,z2,z3,z4,z6]),(0,[z209,z0,z1,z2,z3,z4,z6]),(0,[z349,z31,z0,z1,z2,z3,z6])],[(1,[z0,z1,z2,z3,z4,z167]),(0,[z23,z0,z1,z32,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z350,z6]),(0,[z0,z1,z2,z3,z4,z351,z6]),(0,[z0,z1,z352,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z353,z6])],[(0,[z0,z1,z354,z2,z3,z4,z6]),(0,[z0,z15,z1,z2,z3,z4,z64]),(0,[z19,z0,z1,z2,z3,z4,z6]),(1,[z0,z355,z1,z2,z4,z6])],[(0,[z0,z14,z127,z2,z3,z4,z6]),(0,[z0,z356,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z357,z6]),(0,[z0,z1,z358,z2,z3,z4,z6]),(0,[z0,z157,z1,z2,z32,z4,z6]),(0,[z0,z1,z2,z266,z3,z4,z6])],[(0,[z0,z359,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z360,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z361]),(0,[z0,z15,z2,z78,z3,z4,z6]),(0,[z362,z0,z1,z2,z3,z4,z6])],[(0,[z0,z363,z1,z2,z3,z4,z6]),(0,[z364,z0,z1,z2,z3,z4,z6]),(0,[z43,z0,z1,z2,z365,z4,z6]),(0,[z0,z366,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z104,z6]),(0,[z0,z221,z1,z2,z3,z104,z6]),(0,[z0,z1,z367,z2,z3,z4,z6])],[(1,[z31,z0,z1,z2,z8,z6]),(0,[z233,z0,z1,z2,z3,z4,z6]),(0,[z297,z1,z2,z30,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z368]),(0,[z0,z1,z2,z3,z4,z369,z6]),(0,[z370,z31,z0,z1,z2,z3,z6]),(0,[z371,z0,z1,z2,z20,z3,z6])],[(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z14,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z372,z4,z6])],[(0,[z0,z1,z2,z3,z4,z373,z6]),(0,[z0,z1,z2,z3,z374,z129,z6]),(0,[z0,z85,z1,z2,z3,z4,z6])],[(0,[z31,z35,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z20,z3,z79,z6]),(0,[z0,z1,z55,z2,z3,z4,z173])],[(0,[z23,z0,z1,z2,z3,z76,z6]),(0,[z0,z1,z2,z375,z3,z4,z6]),(0,[z36,z0,z58,z1,z2,z3,z4]),(0,[z0,z2,z30,z3,z4,z97,z6]),(0,[z0,z103,z14,z2,z3,z4,z6]),(0,[z0,z1,z2,z376,z3,z4,z6]),(0,[z377,z0,z1,z2,z3,z4,z6]),(0,[z0,z378,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z379,z6]),(0,[z0,z1,z2,z3,z4,z64,z118])],[(0,[z31,z0,z1,z2,z109,z3,z6]),(0,[z0,z1,z380,z2,z3,z4,z6]),(1,[z0,z67,z2,z3,z97,z6]),(0,[z0,z52,z1,z2,z20,z3,z6]),(1,[z194,z1,z2,z3,z4,z6]),(0,[z0,z1,z381,z2,z3,z4,z6]),(0,[z0,z133,z2,z3,z4,z6,z137])]],
   [[(0,[z0,z1,z2,z3,z4,z49,z6]),(0,[z31,z0,z1,z2,z3,z37,z6]),(0,[z0,z1,z2,z382,z3,z4,z6]),(0,[z0,z1,z2,z383,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z384,z6]),(0,[z0,z1,z131,z3,z199,z4,z6]),(0,[z0,z385,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z11,z113,z6]),(0,[z386,z0,z1,z2,z3,z4,z6])],[(0,[z62,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z49]),(0,[z195,z1,z162,z2,z3,z4,z6]),(0,[z0,z1,z2,z387,z3,z4,z6])],[(0,[z0,z388,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z389]),(0,[z0,z52,z1,z2,z3,z53,z6]),(0,[z0,z1,z2,z3,z390,z4,z6]),(0,[z0,z1,z2,z3,z391,z4,z6])],[(0,[z392,z0,z1,z2,z3,z4,z6]),(0,[z43,z0,z1,z2,z270,z4,z6]),(0,[z0,z1,z2,z3,z4,z393,z6]),(0,[z31,z0,z111,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z394,z4,z6])],[(0,[z0,z39,z1,z2,z3,z395,z6])],[(0,[z0,z1,z2,z3,z4,z396,z6]),(0,[z397,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z72,z2,z3,z4,z293]),(1,[z0,z1,z202,z2,z3,z4]),(0,[z31,z0,z1,z381,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z398]),(0,[z0,z1,z2,z143,z3,z4,z6]),(0,[z0,z58,z1,z2,z3,z4,z113])],[(0,[z0,z1,z2,z20,z3,z6,z65]),(0,[z0,z399,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z400,z6])]],
   [[(0,[z0,z1,z2,z3,z401,z4,z6]),(0,[z0,z402,z1,z2,z3,z4,z6]),(0,[z31,z0,z190,z1,z2,z3,z6]),(0,[z371,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z403,z3,z4,z6]),(0,[z0,z404,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z374,z4,z6]),(0,[z0,z1,z2,z3,z405,z4,z6])],[(0,[z0,z1,z2,z3,z4,z406,z6]),(0,[z60,z1,z162,z2,z3,z4,z6]),(0,[z0,z1,z27,z3,z8,z4,z6]),(0,[z0,z81,z1,z72,z3,z4,z6]),(0,[z407,z0,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z20,z4,z6])],[(0,[z0,z1,z2,z3,z4,z408,z6]),(0,[z0,z1,z2,z3,z409,z4,z6]),(0,[z0,z1,z2,z3,z4,z410,z6]),(1,[z31,z0,z58,z1,z2,z6])],[(0,[z0,z411,z1,z2,z3,z4,z6]),(0,[z412,z0,z1,z2,z3,z4,z6]),(0,[z0,z14,z2,z3,z4,z79,z6]),(0,[z31,z0,z157,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z413,z6]),(0,[z31,z19,z0,z1,z2,z3,z6]),(0,[z414,z31,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z20,z3,z6,z137])],[(1,[z0,z1,z2,z365,z4,z6]),(0,[z0,z415,z1,z2,z3,z4,z6]),(0,[z0,z1,z416,z2,z3,z4,z6]),(0,[z0,z111,z1,z2,z3,z4,z417]),(0,[z0,z1,z2,z20,z3,z251,z6])],[(0,[z31,z0,z60,z1,z2,z3,z6]),(0,[z0,z1,z2,z418,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z65,z91]),(1,[z0,z303,z2,z3,z4,z6]),(0,[z0,z1,z2,z143,z3,z4,z64]),(0,[z419,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z420,z4,z6]),(0,[z0,z1,z2,z3,z4,z421,z6]),(1,[z0,z201,z2,z3,z4,z6]),(0,[z0,z422,z1,z2,z3,z4,z6])]],
   [[(0,[z423,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z424,z2,z3,z4,z6]),(0,[z0,z15,z2,z3,z53,z4,z6])],[(0,[z0,z269,z1,z2,z3,z8,z4]),(0,[z31,z0,z1,z2,z3,z44,z6]),(0,[z0,z1,z2,z3,z425,z4,z6]),(0,[z0,z1,z2,z3,z4,z426,z6]),(0,[z0,z1,z2,z3,z4,z6,z417])],[(0,[z427,z0,z1,z2,z3,z4,z6]),(1,[z0,z111,z1,z3,z112,z6])],[(0,[z36,z0,z1,z2,z143,z3,z4]),(0,[z0,z1,z2,z3,z428,z4,z6]),(0,[z0,z429,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z173])],[(0,[z0,z1,z2,z3,z430,z4,z6]),(0,[z0,z1,z2,z431,z3,z4,z6]),(0,[z0,z14,z2,z78,z3,z4,z6]),(0,[z0,z432,z1,z2,z3,z4,z6]),(0,[z0,z71,z75,z2,z3,z4,z6]),(0,[z433,z0,z1,z2,z3,z4,z6])],[(0,[z434,z0,z1,z2,z3,z4,z6]),(0,[z0,z14,z72,z2,z3,z4,z6]),(0,[z0,z103,z1,z2,z3,z4,z6]),(0,[z0,z435,z1,z2,z3,z4,z6]),(0,[z0,z103,z1,z2,z9,z4,z6]),(1,[z0,z1,z2,z3,z4,z436]),(0,[z0,z1,z131,z2,z3,z4,z6]),(0,[z0,z303,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z9,z6])],[(0,[z0,z437,z1,z2,z3,z4,z6]),(0,[z438,z0,z1,z2,z3,z4,z6]),(0,[z0,z58,z1,z2,z143,z4,z6]),(0,[z0,z439,z1,z2,z3,z4,z6])],[(0,[z0,z440,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z441]),(0,[z0,z1,z2,z3,z4,z442,z6]),(1,[z0,z1,z2,z3,z83,z6]),(0,[z0,z443,z1,z2,z3,z4,z6]),(0,[z0,z15,z1,z2,z3,z4,z160]),(0,[z0,z122,z58,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z436]),(0,[z0,z1,z2,z3,z4,z6,z444])]],
   [[],[(0,[z59,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z445]),(0,[z0,z446,z1,z2,z3,z4,z6]),(0,[z0,z447,z1,z2,z3,z4,z6]),(0,[z0,z448,z1,z2,z3,z4,z6])],[(0,[z0,z1,z449,z2,z3,z4,z6]),(0,[z450,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z30,z3,z4,z79,z6]),(0,[z0,z52,z1,z2,z3,z97,z6])],[(0,[z59,z0,z103,z2,z3,z4,z6]),(0,[z0,z1,z2,z212,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z293]),(0,[z0,z1,z2,z3,z4,z451,z6]),(0,[z0,z1,z2,z3,z314,z4,z6])],[(0,[z452,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z112,z6]),(0,[z31,z0,z1,z2,z3,z199,z6]),(0,[z31,z0,z1,z2,z3,z113,z6])],[(0,[z0,z453,z1,z2,z3,z4,z6]),(0,[z31,z41,z0,z1,z2,z3,z6]),(0,[z0,z1,z202,z2,z3,z4,z97]),(0,[z0,z85,z15,z1,z2,z3,z4]),(0,[z31,z0,z1,z89,z2,z3,z6])],[(1,[z0,z14,z72,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z454])],[(0,[z0,z1,z2,z3,z4,z6,z455]),(0,[z0,z1,z222,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z79,z6,z160])]],
   [[(0,[z0,z456,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z93,z3,z6]),(0,[z0,z1,z2,z3,z4,z457,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z67,z15,z2,z3,z4,z6]),(0,[z458,z0,z1,z2,z3,z4,z6]),(0,[z0,z459,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z460,z4,z6]),(0,[z0,z461,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z6,z462]),(0,[z0,z1,z2,z4,z6,z282,z118])],[(0,[z463,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z464,z4,z6]),(0,[z0,z465,z1,z2,z3,z4,z6]),(0,[z0,z2,z30,z78,z3,z4,z6]),(1,[z0,z1,z2,z4,z216,z6]),(0,[z0,z17,z55,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z6,z90])],[(0,[z0,z1,z2,z466,z3,z4,z6]),(0,[z0,z1,z467,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z78,z3,z6]),(0,[z0,z157,z1,z2,z104,z4,z6]),(0,[z0,z157,z1,z2,z20,z3,z6]),(1,[z31,z0,z1,z55,z2,z6])],[(0,[z0,z1,z2,z468,z3,z4,z6]),(0,[z0,z72,z2,z30,z3,z4,z6]),(0,[z31,z0,z1,z55,z2,z3,z6])],[(0,[z349,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z469,z6]),(0,[z0,z470,z1,z2,z3,z4,z6]),(0,[z0,z471,z1,z2,z3,z4,z6]),(1,[z0,z85,z1,z2,z3,z118])],[(1,[z0,z1,z2,z3,z76,z6]),(0,[z472,z31,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z20,z3,z10,z6])],[(0,[z473,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z8,z9,z4,z6]),(0,[z0,z474,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z344,z20,z3,z6]),(0,[z0,z58,z1,z2,z3,z4,z137])]],
   [[(0,[z475,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z476])],[(1,[z23,z1,z93,z3,z4,z6]),(0,[z41,z1,z2,z3,z4,z42,z6]),(0,[z31,z0,z1,z2,z3,z6,z160])],[(0,[z0,z1,z2,z3,z477,z4,z6]),(0,[z121,z0,z1,z2,z8,z4,z6]),(0,[z1,z2,z3,z44,z4,z42,z6]),(0,[z0,z478,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z479,z6]),(0,[z0,z1,z480,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z205,z6]),(0,[z0,z1,z2,z3,z119,z4,z6])],[(0,[z23,z31,z0,z1,z2,z3,z6]),(1,[z0,z103,z2,z129,z4,z6])],[(0,[z23,z0,z157,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z481,z4,z6]),(0,[z0,z1,z2,z482,z3,z4,z6]),(0,[z0,z122,z1,z2,z143,z3,z4]),(0,[z370,z0,z1,z2,z3,z4,z6]),(0,[z0,z111,z235,z2,z3,z4,z6]),(0,[z0,z111,z1,z2,z3,z199,z6]),(0,[z0,z359,z1,z2,z20,z3,z6])],[(0,[z0,z483,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z8,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z484]),(0,[z0,z1,z2,z3,z485,z4,z6]),(0,[z0,z111,z1,z2,z3,z4,z379])],[(0,[z0,z486,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z487,z4,z6]),(0,[z0,z488,z1,z2,z3,z4,z6]),(0,[z0,z489,z1,z2,z3,z4,z6]),(0,[z0,z81,z2,z30,z3,z4,z6]),(0,[z0,z2,z78,z3,z129,z4,z6]),(0,[z490,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z491])],[(0,[z0,z1,z2,z492,z3,z4,z6]),(0,[z493,z0,z1,z2,z3,z4,z6]),(0,[z0,z67,z52,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z216,z6]),(0,[z0,z1,z2,z3,z494,z4,z6]),(0,[z0,z1,z2,z495,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z3,z6]),(0,[z0,z1,z2,z496,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z497,z4,z6]),(0,[z498,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z365,z3,z4,z6]),(0,[z0,z1,z499,z2,z3,z4,z6]),(0,[z0,z52,z2,z3,z53,z4,z6]),(0,[z0,z1,z2,z3,z500,z4,z6]),(0,[z0,z1,z2,z3,z86,z6,z118])],[(0,[z62,z0,z127,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z501,z4,z6]),(0,[z0,z1,z2,z502,z3,z4,z6]),(0,[z0,z157,z1,z2,z3,z4,z6]),(0,[z0,z157,z1,z2,z9,z4,z6]),(0,[z0,z85,z1,z2,z20,z3,z6])],[(0,[z7,z121,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z503,z6]),(0,[z0,z1,z2,z3,z4,z504,z6]),(0,[z0,z1,z2,z3,z4,z505,z6])],[(0,[z0,z103,z1,z2,z129,z4,z6])],[(1,[z62,z127,z2,z3,z4,z6]),(0,[z0,z506,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z507]),(0,[z0,z1,z2,z3,z4,z6,z508])],[(0,[z0,z509,z1,z2,z3,z4,z6]),(0,[z0,z510,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z511]),(0,[z31,z0,z1,z2,z3,z119,z6]),(0,[z0,z1,z2,z3,z512,z4,z6])],[(0,[z62,z0,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z513,z4,z6]),(0,[z514,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z131,z2,z3,z112,z6]),(0,[z0,z1,z3,z199,z4,z112,z6]),(0,[z0,z1,z2,z515,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z516,z6]),(0,[z0,z1,z2,z3,z4,z517,z6]),(0,[z0,z1,z2,z3,z395,z4,z6]),(0,[z0,z1,z2,z3,z4,z518,z6]),(0,[z0,z1,z2,z143,z3,z4,z91]),(0,[z0,z1,z2,z519,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z520,z4,z6]),(0,[z0,z521,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z522,z6]),(1,[z31,z0,z1,z2,z20,z6]),(0,[z0,z523,z1,z2,z3,z4,z6]),(0,[z0,z58,z1,z2,z9,z4,z6]),(0,[z0,z58,z1,z2,z3,z4,z6])],[(0,[z524,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z525,z2,z3,z4,z6]),(0,[z0,z526,z1,z2,z3,z4,z6])],[(0,[z0,z527,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z241,z3,z4]),(0,[z0,z1,z2,z3,z528,z4,z6]),(0,[z31,z0,z1,z2,z30,z3,z6]),(0,[z0,z1,z2,z3,z4,z529,z6]),(0,[z0,z1,z2,z20,z3,z199,z6]),(1,[z0,z385,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z530,z4,z6]),(1,[z0,z1,z89,z3,z4,z91]),(0,[z0,z1,z2,z143,z20,z3,z6])],[(0,[z0,z531,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z532,z4,z6]),(1,[z1,z2,z29,z3,z4,z6]),(0,[z0,z1,z2,z3,z533,z4,z6]),(1,[z0,z1,z2,z3,z395,z6]),(0,[z31,z19,z1,z2,z3,z4,z6]),(0,[z31,z0,z58,z1,z2,z4,z6]),(0,[z0,z355,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z534,z6]),(0,[z31,z43,z0,z1,z2,z3,z6]),(0,[z0,z261,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z535]),(1,[z0,z58,z1,z2,z4,z137])],[(0,[z0,z1,z2,z109,z3,z4,z6]),(0,[z0,z1,z2,z109,z9,z4,z6]),(0,[z414,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z176,z6])],[(1,[z195,z1,z162,z3,z4,z6]),(1,[z0,z1,z2,z482,z3,z4]),(1,[z0,z1,z2,z3,z99,z6]),(0,[z0,z1,z2,z3,z4,z536,z6])]],
   [[(0,[z0,z1,z537,z2,z3,z4,z6]),(0,[z121,z0,z1,z2,z3,z140,z6]),(0,[z0,z58,z1,z2,z3,z4,z64])],[(0,[z0,z1,z2,z3,z538,z4,z6]),(0,[z539,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z540,z6]),(0,[z0,z1,z2,z3,z4,z6,z541]),(0,[z0,z122,z15,z2,z3,z4,z6]),(0,[z31,z31,z0,z1,z2,z3,z6])],[(0,[z0,z542,z1,z2,z3,z4,z6]),(0,[z543,z0,z1,z2,z3,z4,z6]),(0,[z0,z544,z1,z2,z3,z4,z6]),(0,[z0,z1,z55,z2,z3,z4,z436]),(1,[z0,z75,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z4,z113,z6])],[(0,[z0,z1,z127,z2,z20,z3,z6]),(0,[z0,z1,z2,z545,z3,z4,z6]),(0,[z0,z546,z1,z2,z3,z4,z6])],[(0,[z547,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z548,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z53,z4,z6]),(0,[z0,z1,z2,z549,z3,z4,z6]),(1,[z0,z1,z2,z20,z9,z6])],[(0,[z62,z1,z162,z2,z3,z4,z6]),(0,[z0,z14,z60,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z550]),(0,[z0,z1,z2,z551,z3,z4,z6]),(0,[z0,z1,z552,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z64,z6])],[(0,[z62,z0,z103,z2,z3,z4,z6]),(1,[z0,z269,z1,z2,z3,z4]),(0,[z553,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z132,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z554]),(0,[z555,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z556,z6])],[(0,[z0,z1,z557,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z3,z44,z6]),(0,[z427,z0,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z558,z20,z3,z6]),(0,[z0,z559,z1,z2,z20,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z560,z6]),(0,[z0,z102,z1,z3,z8,z4,z6]),(0,[z31,z0,z1,z72,z2,z3,z6])],[(0,[z59,z0,z127,z2,z3,z4,z6]),(0,[z195,z0,z157,z1,z3,z4,z6]),(0,[z0,z1,z2,z561,z3,z4,z6]),(0,[z0,z562,z1,z2,z3,z4,z6]),(0,[z0,z1,z55,z32,z3,z4,z6]),(0,[z0,z1,z2,z3,z563,z4,z6]),(0,[z564,z0,z1,z2,z3,z4,z6]),(0,[z0,z565,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z86,z6])],[(0,[z0,z60,z2,z30,z3,z4,z6]),(0,[z7,z1,z2,z3,z8,z4,z6]),(0,[z0,z1,z2,z3,z4,z566,z6]),(0,[z0,z1,z567,z2,z3,z4,z6]),(0,[z0,z568,z1,z2,z3,z4,z6]),(0,[z0,z103,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z4,z83,z6]),(0,[z0,z1,z131,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z4,z569,z6])],[(0,[z0,z1,z2,z3,z4,z97,z6]),(0,[z0,z85,z1,z2,z3,z4,z118])],[(0,[z0,z1,z2,z3,z4,z6,z570]),(0,[z571,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z572,z3,z4,z6]),(0,[z31,z0,z39,z1,z2,z3,z6]),(0,[z0,z1,z2,z573,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z10,z6]),(0,[z0,z1,z2,z20,z3,z6,z179])],[(0,[z59,z0,z1,z2,z20,z3,z6]),(0,[z574,z0,z1,z2,z3,z4,z6]),(0,[z0,z575,z1,z2,z3,z4,z6]),(0,[z0,z39,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z576]),(0,[z0,z39,z1,z2,z9,z4,z6]),(0,[z0,z1,z2,z20,z3,z6,z91]),(0,[z31,z0,z1,z2,z3,z6,z118]),(0,[z0,z577,z1,z2,z3,z4,z6])],[(0,[z62,z0,z2,z78,z3,z4,z6]),(0,[z0,z1,z2,z32,z109,z4,z6]),(1,[z0,z183,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z578,z6]),(0,[z0,z1,z2,z3,z4,z579,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z580,z6]),(0,[z0,z1,z2,z3,z581,z4,z6]),(0,[z0,z1,z2,z3,z4,z64,z86]),(0,[z0,z582,z1,z2,z3,z4,z6])],[(0,[z0,z1,z127,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z112,z6])],[(0,[z121,z1,z2,z3,z4,z42,z6]),(0,[z583,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z417]),(0,[z584,z0,z1,z2,z3,z4,z6])],[(0,[z585,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z199,z44,z6]),(0,[z0,z1,z2,z32,z20,z3,z6]),(0,[z0,z1,z89,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z119,z6])],[(0,[z0,z586,z1,z2,z3,z4,z6]),(0,[z195,z0,z1,z32,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z587,z6]),(1,[z0,z2,z339,z3,z4,z6]),(1,[z0,z1,z131,z3,z199,z6]),(0,[z0,z1,z2,z588,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z462]),(0,[z0,z1,z2,z3,z4,z6,z589])],[(0,[z0,z1,z2,z590,z3,z4,z6]),(0,[z0,z1,z2,z558,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z591]),(0,[z0,z559,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z592,z3,z4,z6]),(0,[z0,z593,z1,z2,z3,z4,z6])],[(0,[z0,z594,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z374,z6]),(0,[z595,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z11,z4,z6])]],
   [[(0,[z0,z1,z596,z2,z3,z4,z6]),(0,[z472,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z281]),(0,[z0,z1,z2,z3,z4,z597,z6])],[(0,[z41,z0,z1,z2,z3,z42,z6]),(0,[z0,z1,z2,z482,z3,z129,z4]),(0,[z0,z58,z15,z1,z2,z3,z4]),(0,[z0,z598,z1,z2,z3,z4,z6]),(0,[z599,z0,z1,z2,z3,z4,z6])],[(0,[z600,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z601,z6]),(0,[z0,z1,z2,z3,z602,z4,z6]),(0,[z31,z0,z15,z1,z2,z3,z6]),(0,[z0,z1,z2,z20,z3,z104,z6]),(0,[z0,z1,z2,z603,z3,z4,z6])],[(0,[z23,z0,z222,z2,z3,z4,z6]),(0,[z43,z121,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z604,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z605]),(0,[z0,z606,z1,z2,z3,z4,z6]),(0,[z0,z103,z2,z3,z4,z79,z6]),(0,[z0,z1,z2,z3,z184,z4,z6]),(1,[z31,z190,z1,z2,z3,z6])],[(0,[z0,z1,z2,z8,z104,z4,z6]),(0,[z0,z1,z2,z3,z4,z607,z6]),(0,[z0,z1,z2,z3,z4,z608,z6])],[(0,[z23,z0,z1,z2,z3,z4,z6]),(1,[z121,z1,z2,z109,z4,z6]),(0,[z31,z36,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z113,z6,z462])],[(0,[z0,z609,z1,z2,z3,z4,z6])],[(0,[z121,z1,z2,z109,z3,z4,z6]),(0,[z0,z2,z78,z3,z4,z79,z6]),(0,[z31,z0,z301,z1,z2,z3,z6]),(0,[z610,z0,z1,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z6,z117])]],
   [[(0,[z0,z1,z2,z611,z3,z4,z6]),(1,[z43,z1,z2,z3,z44,z6]),(0,[z0,z1,z2,z3,z612,z4,z6]),(0,[z0,z15,z1,z2,z143,z3,z4]),(0,[z0,z1,z2,z47,z3,z4,z6])],[(0,[z613,z0,z1,z2,z3,z4,z6]),(0,[z1,z162,z2,z93,z3,z4,z6]),(0,[z0,z614,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z37,z6]),(1,[z0,z1,z341,z2,z3,z4]),(0,[z0,z1,z2,z32,z3,z4,z6]),(0,[z0,z190,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z615,z4,z6])],[(0,[z0,z616,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z617,z6]),(0,[z0,z1,z2,z3,z4,z618,z6])],[(0,[z0,z619,z1,z2,z3,z4,z6]),(0,[z620,z0,z1,z2,z3,z4,z6]),(0,[z621,z0,z1,z2,z3,z4,z6])],[(0,[z59,z60,z1,z2,z3,z4,z6]),(1,[z0,z102,z1,z3,z4,z6]),(0,[z35,z0,z1,z2,z3,z4,z65]),(0,[z0,z1,z2,z3,z4,z622,z6]),(0,[z0,z1,z2,z492,z20,z3,z6])],[(1,[z171,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z623]),(0,[z0,z1,z2,z3,z199,z42,z6]),(0,[z0,z624,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z20,z3,z6]),(1,[z0,z133,z2,z3,z4,z6])],[(0,[z23,z0,z1,z2,z3,z501,z6]),(0,[z0,z1,z2,z3,z625,z4,z6]),(0,[z41,z0,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z42,z6]),(0,[z0,z626,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z627,z6]),(0,[z0,z1,z2,z628,z3,z4,z6]),(0,[z0,z1,z2,z629,z3,z4,z6]),(0,[z0,z630,z1,z2,z3,z4,z6]),(0,[z31,z190,z1,z2,z3,z4,z6])],[(0,[z59,z0,z2,z78,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z79,z6]),(0,[z31,z0,z157,z1,z2,z3,z6]),(1,[z31,z19,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z631,z6])]],
   [[(0,[z0,z1,z2,z3,z632,z4,z6]),(0,[z31,z0,z52,z1,z2,z3,z6]),(0,[z0,z459,z1,z2,z4,z112,z6])],[(0,[z0,z1,z2,z3,z4,z6,z633]),(0,[z31,z0,z1,z2,z3,z53,z6]),(0,[z0,z58,z1,z2,z3,z4,z91]),(0,[z0,z1,z2,z3,z4,z6,z634])],[(0,[z0,z635,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z8,z4,z42,z6]),(0,[z0,z1,z2,z636,z3,z4,z6]),(0,[z0,z103,z1,z2,z78,z4,z6]),(1,[z0,z1,z2,z3,z56,z6]),(0,[z0,z92,z2,z3,z4,z6,z118])],[(0,[z0,z1,z2,z637,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z638]),(0,[z0,z639,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z640,z6])],[(0,[z35,z0,z1,z2,z20,z3,z6]),(0,[z0,z1,z641,z2,z3,z4,z6]),(0,[z0,z1,z55,z2,z3,z99,z6]),(0,[z0,z1,z2,z3,z642,z4,z6]),(0,[z0,z1,z2,z643,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z6,z118])],[(0,[z0,z58,z1,z2,z20,z3,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z644,z1,z2,z3,z4,z6]),(0,[z645,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z78,z3,z4,z6]),(0,[z0,z646,z1,z2,z3,z4,z6]),(0,[z0,z1,z647,z2,z20,z3,z6])]],
   [[(0,[z23,z0,z1,z2,z289,z4,z6]),(0,[z31,z7,z0,z1,z2,z3,z6]),(0,[z0,z1,z72,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z65]),(0,[z0,z1,z648,z2,z3,z4,z6]),(0,[z649,z0,z1,z2,z3,z4,z6]),(0,[z0,z157,z1,z3,z104,z4,z6]),(1,[z0,z235,z2,z3,z4,z6])],[(0,[z0,z1,z650,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z44,z6]),(0,[z0,z1,z2,z3,z651,z4,z6]),(0,[z0,z183,z1,z2,z4,z97,z6]),(0,[z0,z122,z1,z2,z3,z119,z4]),(0,[z0,z1,z2,z3,z199,z4,z6]),(1,[z0,z1,z2,z3,z4,z379]),(0,[z194,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z652,z6])],[(0,[z43,z1,z2,z3,z8,z4,z6]),(0,[z0,z1,z2,z109,z104,z4,z6]),(0,[z0,z1,z2,z109,z20,z3,z6]),(0,[z297,z0,z1,z2,z3,z4,z6]),(0,[z0,z261,z1,z2,z3,z129,z6]),(0,[z0,z221,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z653,z2,z3,z4,z6])],[(0,[z0,z654,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z143,z4,z113])],[(0,[z23,z0,z1,z93,z3,z4,z6]),(0,[z1,z2,z109,z3,z8,z4,z6]),(0,[z31,z0,z1,z2,z3,z8,z6]),(1,[z0,z1,z2,z4,z258,z6]),(0,[z0,z1,z2,z3,z4,z655,z6])],[(0,[z0,z127,z2,z30,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z656]),(0,[z0,z14,z1,z72,z3,z4,z6]),(0,[z0,z122,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z91,z118]),(0,[z0,z1,z2,z20,z3,z9,z6]),(0,[z0,z1,z2,z3,z4,z6,z137])],[(0,[z0,z657,z1,z2,z3,z4,z6]),(0,[z23,z36,z1,z2,z3,z4,z6]),(0,[z0,z658,z1,z2,z3,z4,z6]),(0,[z659,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z55,z2,z32,z4,z6])]],
   [[(0,[z31,z0,z14,z1,z2,z3,z6]),(0,[z0,z1,z2,z660,z3,z4,z6]),(0,[z0,z1,z2,z3,z119,z86,z6])],[(1,[z0,z1,z2,z3,z140,z6]),(0,[z31,z0,z103,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z661,z4,z6]),(0,[z0,z1,z2,z3,z119,z4,z118]),(0,[z0,z1,z2,z3,z4,z662,z6])],[(0,[z35,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z663,z4,z6]),(0,[z0,z1,z2,z3,z4,z86,z91]),(0,[z138,z31,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z664,z4,z6]),(0,[z0,z1,z2,z3,z4,z665,z6]),(0,[z31,z0,z1,z2,z3,z6,z554]),(0,[z0,z385,z1,z2,z3,z6,z137])],[],[(0,[z0,z1,z2,z666,z3,z4,z6]),(0,[z0,z667,z1,z2,z3,z4,z6]),(0,[z0,z15,z2,z3,z4,z6,z160]),(0,[z0,z122,z1,z2,z3,z4,z79]),(0,[z0,z1,z2,z3,z4,z6,z668]),(0,[z0,z1,z2,z20,z3,z113,z6]),(0,[z0,z1,z647,z2,z3,z4,z6])],[(0,[z669,z0,z1,z2,z3,z4,z6]),(0,[z0,z15,z2,z30,z3,z4,z6]),(0,[z0,z1,z2,z670,z3,z4,z6]),(0,[z0,z671,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z86,z6]),(1,[z0,z2,z3,z4,z6,z278])],[(0,[z31,z62,z0,z1,z2,z3,z6]),(0,[z0,z1,z672,z2,z3,z4,z6]),(0,[z0,z71,z1,z3,z4,z64,z6])]],
   [[(0,[z62,z0,z60,z2,z3,z4,z6]),(0,[z0,z67,z2,z3,z4,z97,z6]),(0,[z31,z0,z1,z2,z3,z97,z6]),(0,[z0,z2,z3,z4,z6,z278,z137]),(0,[z0,z1,z2,z4,z113,z6,z137]),(0,[z0,z355,z1,z2,z4,z6,z118])],[(0,[z0,z1,z341,z2,z3,z4,z6]),(1,[z0,z122,z2,z3,z4,z79]),(0,[z31,z0,z85,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z673,z6]),(0,[z0,z1,z2,z3,z4,z674,z6]),(0,[z675,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z258,z6])],[(0,[z0,z1,z2,z676,z3,z4,z6]),(0,[z0,z677,z1,z2,z3,z4,z6]),(0,[z0,z39,z1,z2,z20,z3,z6]),(0,[z0,z111,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z333,z6])],[(0,[z0,z1,z678,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z679,z4,z6]),(0,[z0,z1,z89,z2,z3,z4,z91]),(0,[z0,z1,z89,z3,z4,z6,z91]),(0,[z0,z1,z2,z3,z4,z680,z6])],[(0,[z0,z681,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z682,z6])],[(0,[z0,z1,z2,z683,z3,z4,z6]),(0,[z23,z0,z144,z2,z3,z4,z6]),(0,[z0,z144,z1,z2,z3,z4,z6]),(0,[z0,z684,z1,z2,z3,z4,z6]),(0,[z0,z81,z14,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z685])],[(0,[z0,z1,z2,z3,z686,z4,z6]),(0,[z0,z1,z2,z3,z4,z687,z6]),(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z1,z2,z3,z4,z688,z6]),(0,[z0,z1,z689,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z89,z2,z20,z3,z6]),(0,[z0,z71,z1,z2,z3,z4,z91])],[(0,[z0,z1,z690,z2,z3,z4,z6]),(0,[z23,z0,z1,z2,z3,z4,z167]),(0,[z0,z1,z2,z691,z3,z4,z6]),(1,[z0,z157,z1,z104,z4,z6])],[(0,[z0,z1,z2,z3,z692,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z65]),(0,[z0,z1,z2,z693,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z6,z160]),(1,[z0,z459,z1,z2,z4,z6])],[(0,[z694,z0,z1,z2,z3,z4,z6]),(0,[z7,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z695,z2,z3,z4,z6]),(0,[z0,z67,z1,z2,z20,z3,z6]),(0,[z0,z55,z2,z339,z3,z4,z6])],[(0,[z23,z0,z1,z162,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z696]),(0,[z0,z1,z2,z3,z697,z4,z6]),(0,[z0,z71,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z4,z698,z6])],[(0,[z31,z0,z1,z127,z2,z3,z6]),(0,[z1,z162,z2,z3,z4,z37,z6]),(0,[z0,z1,z2,z3,z4,z6,z699]),(0,[z0,z1,z2,z700,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z701]),(1,[z31,z0,z1,z2,z10,z6])],[(1,[z0,z1,z2,z3,z501,z6]),(0,[z23,z1,z2,z93,z3,z4,z6]),(0,[z43,z41,z1,z2,z3,z4,z6]),(0,[z0,z702,z1,z2,z3,z4,z6]),(0,[z0,z703,z1,z2,z3,z4,z6])],[(0,[z121,z0,z1,z2,z3,z4,z6]),(0,[z0,z704,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z705,z6]),(0,[z0,z67,z1,z2,z3,z53,z6]),(0,[z0,z1,z2,z3,z706,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z707,z4,z6]),(0,[z23,z31,z1,z93,z3,z6])],[(0,[z0,z708,z2,z3,z4,z6]),(0,[z0,z709,z1,z2,z3,z4]),(0,[z31,z0,z102,z1,z8,z6]),(0,[z0,z2,z3,z4,z6,z710]),(0,[z31,z190,z1,z2,z109,z6]),(0,[z0,z1,z2,z3,z56,z6]),(0,[z0,z1,z2,z9,z56,z6])],[(0,[z23,z1,z468,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z711]),(0,[z0,z1,z2,z20,z270,z6]),(0,[z0,z459,z1,z2,z44,z6])],[(0,[z0,z1,z2,z3,z712,z6]),(0,[z0,z52,z2,z3,z481,z6]),(0,[z31,z0,z103,z301,z2,z6]),(0,[z0,z1,z2,z3,z4,z713])],[(0,[z0,z1,z2,z3,z4,z714]),(0,[z0,z1,z2,z3,z6,z715]),(0,[z31,z0,z559,z1,z2,z6])],[(0,[z31,z0,z1,z27,z3,z6]),(0,[z0,z1,z2,z4,z716,z6]),(0,[z0,z717,z2,z3,z4,z6]),(0,[z0,z17,z2,z3,z56,z6]),(0,[z31,z0,z355,z1,z2,z6])],[(0,[z0,z1,z2,z3,z718,z6]),(0,[z0,z1,z2,z719,z4,z6]),(0,[z0,z102,z201,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z720])],[(0,[z62,z721,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z722,z6]),(0,[z0,z1,z2,z4,z723,z6]),(0,[z31,z0,z1,z55,z2,z436]),(0,[z0,z724,z1,z2,z4,z6]),(0,[z0,z1,z89,z20,z3,z91])]],
   [[(0,[z0,z1,z2,z3,z725,z6]),(0,[z121,z1,z2,z365,z4,z6]),(0,[z0,z2,z726,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z727]),(0,[z0,z14,z72,z3,z4,z293]),(0,[z0,z1,z2,z216,z83,z6]),(0,[z0,z157,z1,z20,z104,z6]),(0,[z0,z1,z2,z3,z287,z86]),(0,[z0,z1,z2,z143,z20,z113])],[(0,[z0,z1,z2,z3,z728,z6]),(0,[z0,z1,z480,z3,z4,z64]),(0,[z31,z0,z17,z2,z3,z6]),(0,[z194,z1,z89,z3,z4,z91]),(0,[z194,z1,z2,z143,z3,z4]),(0,[z31,z19,z1,z2,z113,z6]),(0,[z0,z729,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z730,z6]),(0,[z0,z646,z30,z3,z4,z6])],[(0,[z195,z1,z162,z20,z3,z6]),(0,[z0,z15,z2,z3,z4,z136]),(0,[z0,z731,z2,z3,z4,z6]),(0,[z0,z385,z2,z3,z6,z278])],[(0,[z31,z0,z1,z2,z340,z6]),(0,[z1,z2,z3,z732,z4,z6]),(0,[z0,z15,z2,z3,z4,z633]),(0,[z31,z190,z157,z1,z2,z6]),(0,[z0,z1,z2,z4,z258,z6]),(0,[z0,z1,z2,z3,z6,z733]),(0,[z0,z1,z131,z3,z734,z6]),(0,[z1,z2,z20,z3,z6,z90]),(0,[z0,z1,z2,z3,z4,z735])],[(0,[z0,z1,z2,z3,z181,z6]),(0,[z31,z19,z1,z2,z109,z6]),(0,[z0,z1,z341,z2,z20,z3]),(0,[z31,z0,z1,z2,z3,z184]),(0,[z0,z2,z736,z3,z4,z6]),(0,[z0,z737,z2,z3,z4,z6])],[(0,[z0,z738,z2,z3,z4,z6]),(0,[z0,z1,z2,z739,z4,z6]),(0,[z0,z1,z2,z740,z3,z6])],[(0,[z0,z1,z3,z4,z741,z6]),(0,[z0,z742,z2,z3,z4,z6]),(0,[z190,z1,z2,z3,z4,z6]),(1,[z1,z2,z3,z743,z6]),(0,[z1,z2,z3,z4,z744,z6]),(0,[z31,z0,z220,z1,z2,z6]),(0,[z0,z1,z55,z32,z56,z6]),(0,[z0,z85,z2,z3,z117,z118])]],
   [[(0,[z0,z2,z78,z664,z4,z6]),(0,[z31,z0,z1,z2,z664,z6]),(0,[z31,z0,z704,z1,z2,z6]),(0,[z0,z1,z745,z2,z3,z4]),(0,[z0,z1,z2,z3,z6,z746])],[(0,[z0,z147,z1,z3,z4,z64]),(0,[z0,z15,z2,z3,z4,z160]),(0,[z0,z1,z747,z2,z3,z6]),(0,[z0,z748,z2,z3,z4,z6]),(0,[z0,z359,z459,z1,z2,z6]),(0,[z0,z1,z2,z3,z6,z749])],[(0,[z62,z677,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z750]),(0,[z35,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z3,z4,z751]),(0,[z0,z752,z2,z3,z4,z6])],[(0,[z0,z103,z2,z686,z4,z6]),(0,[z60,z2,z240,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z753]),(0,[z0,z754,z2,z3,z4,z6]),(0,[z0,z15,z2,z502,z3,z4]),(0,[z0,z1,z2,z3,z4,z755]),(0,[z0,z756,z2,z3,z4,z6]),(0,[z31,z0,z757,z1,z2,z3])],[(0,[z0,z1,z2,z4,z758,z6]),(0,[z0,z459,z1,z2,z42,z6]),(0,[z0,z1,z759,z3,z4,z6]),(0,[z472,z0,z1,z2,z3,z176]),(0,[z0,z58,z1,z2,z20,z137])],[(0,[z0,z1,z2,z3,z760,z6]),(0,[z7,z1,z2,z732,z4,z6]),(0,[z0,z1,z2,z3,z4,z761]),(0,[z0,z1,z2,z3,z762,z6]),(0,[z31,z0,z1,z2,z3,z73]),(0,[z0,z763,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z764]),(0,[z60,z721,z2,z3,z4,z6]),(0,[z0,z765,z1,z2,z3,z6]),(0,[z31,z0,z1,z2,z3,z167]),(0,[z0,z1,z32,z520,z4,z6]),(0,[z0,z1,z3,z4,z6,z766]),(0,[z31,z0,z1,z641,z2,z6]),(0,[z0,z767,z1,z2,z4,z6]),(0,[z31,z0,z1,z2,z674,z6]),(0,[z0,z1,z2,z768,z4,z6]),(0,[z31,z0,z1,z2,z258,z6]),(0,[z0,z2,z3,z769,z4,z6]),(0,[z0,z770,z2,z3,z4,z6]),(0,[z0,z133,z2,z3,z6,z281])],[(0,[z171,z0,z1,z27,z3,z6]),(0,[z0,z58,z1,z2,z487,z4])]],
   [[(0,[z0,z122,z2,z3,z4,z79]),(0,[z0,z15,z2,z3,z4,z771]),(0,[z0,z1,z244,z3,z4,z91]),(0,[z31,z19,z157,z1,z2,z6]),(0,[z0,z1,z2,z3,z772,z6]),(0,[z31,z194,z1,z2,z3,z6])],[(0,[z0,z1,z3,z4,z773,z6]),(0,[z0,z1,z2,z20,z40,z6]),(0,[z0,z2,z3,z4,z774,z6]),(0,[z0,z775,z1,z2,z4,z6]),(0,[z0,z776,z1,z2,z4,z6]),(0,[z0,z221,z1,z2,z3,z6])],[(0,[z0,z222,z2,z3,z4,z6]),(0,[z0,z1,z2,z40,z501,z6]),(0,[z31,z0,z1,z2,z289,z6]),(0,[z0,z777,z1,z3,z4,z6]),(0,[z0,z1,z778,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z779]),(0,[z19,z1,z2,z20,z3,z6]),(0,[z0,z85,z1,z2,z3,z735])],[(0,[z0,z1,z2,z3,z4,z780]),(0,[z0,z1,z27,z3,z181,z6]),(0,[z19,z1,z2,z3,z42,z6]),(0,[z0,z781,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z782]),(0,[z31,z0,z1,z232,z2,z6]),(0,[z0,z2,z783,z3,z4,z6]),(0,[z31,z0,z1,z2,z383,z6]),(0,[z31,z0,z565,z1,z2,z6]),(0,[z0,z2,z784,z20,z3,z6])],[(0,[z0,z71,z303,z3,z4,z64]),(0,[z0,z2,z3,z4,z6,z785])],[(0,[z23,z1,z93,z3,z76,z6]),(0,[z0,z2,z3,z4,z786,z6]),(0,[z0,z1,z2,z787,z4,z6]),(0,[z31,z0,z58,z1,z2,z554])],[(0,[z0,z1,z2,z3,z4,z788]),(0,[z171,z1,z2,z3,z42,z6]),(0,[z0,z264,z1,z2,z3,z118]),(0,[z0,z58,z1,z2,z4,z208])]],
   [[(0,[z0,z1,z2,z4,z789,z6]),(0,[z0,z1,z186,z32,z4,z6]),(0,[z564,z1,z2,z3,z44,z6]),(0,[z36,z1,z2,z3,z4,z65]),(0,[z0,z17,z2,z3,z4,z6]),(0,[z0,z2,z78,z790,z4,z6]),(0,[z0,z791,z1,z2,z3,z6]),(0,[z0,z15,z352,z2,z3,z4]),(0,[z0,z2,z339,z20,z3,z6]),(0,[z0,z17,z2,z9,z4,z6]),(0,[z0,z1,z2,z792,z4,z6]),(0,[z31,z0,z1,z2,z3,z793])],[(0,[z0,z1,z2,z3,z4,z794]),(0,[z7,z2,z212,z8,z4,z6]),(0,[z0,z459,z1,z2,z4,z6]),(0,[z31,z0,z45,z1,z2,z6]),(0,[z0,z1,z3,z768,z4,z6]),(0,[z0,z1,z2,z3,z99,z173])],[(0,[z0,z1,z2,z3,z4,z795]),(0,[z31,z0,z1,z2,z661,z6])],[(0,[z0,z222,z2,z3,z501,z6]),(0,[z31,z0,z1,z2,z3,z49]),(0,[z0,z796,z2,z3,z4,z6]),(0,[z0,z92,z2,z3,z4,z91]),(0,[z31,z797,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z798,z6])],[(0,[z31,z0,z2,z212,z3,z6]),(0,[z0,z269,z1,z2,z9,z4]),(0,[z0,z799,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z800]),(0,[z31,z0,z1,z2,z253,z6]),(0,[z0,z261,z39,z1,z2,z6]),(0,[z0,z1,z2,z3,z4,z801]),(0,[z31,z802,z1,z2,z3,z6]),(0,[z0,z2,z20,z3,z769,z6])],[(0,[z0,z1,z2,z3,z501,z6]),(0,[z7,z171,z1,z2,z8,z6]),(0,[z7,z1,z2,z20,z8,z6]),(0,[z31,z0,z58,z15,z1,z2])],[(1,[z31,z0,z102,z1,z6]),(0,[z31,z0,z269,z1,z2,z6]),(0,[z0,z1,z2,z3,z4,z803]),(0,[z0,z261,z1,z2,z3,z6]),(0,[z0,z183,z1,z2,z20,z6]),(0,[z31,z0,z92,z2,z3,z6]),(0,[z0,z58,z2,z4,z278,z137])],[(0,[z0,z804,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z805,z6]),(0,[z31,z0,z1,z695,z2,z6]),(0,[z0,z1,z653,z3,z4,z91]),(0,[z0,z92,z2,z20,z3,z6])]],
   [[(0,[z19,z1,z2,z3,z4,z6]),(0,[z0,z806,z1,z2,z3,z4]),(0,[z31,z0,z2,z3,z807,z6])],[(0,[z31,z0,z808,z2,z3,z6]),(0,[z31,z0,z1,z2,z48,z6])],[(0,[z0,z1,z27,z3,z4,z6]),(0,[z0,z1,z141,z3,z4,z91]),(1,[z0,z1,z2,z4,z809])],[(0,[z31,z62,z0,z103,z2,z6]),(0,[z31,z0,z1,z341,z2,z3]),(0,[z31,z0,z254,z1,z2,z6]),(0,[z810,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z811,z6])],[(0,[z41,z1,z2,z3,z42,z6]),(0,[z0,z1,z2,z4,z6,z282]),(0,[z0,z133,z2,z143,z3,z4])],[(0,[z0,z222,z2,z289,z4,z6]),(0,[z0,z812,z1,z2,z3,z6]),(0,[z0,z67,z2,z3,z309,z6]),(0,[z0,z202,z2,z3,z53,z4]),(0,[z31,z0,z58,z1,z2,z113])],[(0,[z0,z813,z2,z3,z4,z6]),(0,[z0,z814,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z69,z6]),(0,[z0,z1,z2,z3,z815,z6]),(0,[z0,z103,z2,z20,z129,z6]),(0,[z31,z0,z122,z2,z3,z79])],[(0,[z0,z1,z2,z816,z4,z6]),(0,[z0,z1,z2,z289,z4,z6]),(0,[z31,z0,z1,z2,z533,z6]),(0,[z0,z39,z2,z78,z4,z6]),(0,[z0,z817,z2,z3,z4,z6]),(0,[z31,z818,z1,z2,z3,z6]),(0,[z0,z819,z2,z3,z4,z6])]],
   [[(0,[z31,z0,z14,z72,z3,z6]),(0,[z190,z1,z2,z3,z112,z6]),(0,[z31,z0,z75,z2,z3,z6]),(0,[z31,z19,z58,z1,z2,z6])],[(0,[z0,z1,z2,z3,z4,z820]),(0,[z0,z1,z2,z3,z821,z6]),(0,[z0,z2,z3,z4,z6,z822]),(0,[z31,z0,z1,z823,z3,z6]),(0,[z371,z1,z2,z492,z3,z6])],[(0,[z297,z1,z2,z3,z4,z6]),(0,[z19,z1,z2,z3,z155,z6]),(0,[z0,z1,z2,z3,z824,z6])],[(0,[z59,z60,z2,z3,z4,z6]),(0,[z0,z825,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z712,z6]),(0,[z0,z826,z2,z3,z4,z6]),(0,[z0,z111,z1,z3,z112,z417])],[(0,[z0,z1,z2,z3,z827,z6]),(0,[z0,z1,z3,z828,z4,z6]),(0,[z0,z1,z2,z3,z829,z4]),(0,[z0,z1,z2,z241,z3,z181]),(0,[z284,z0,z1,z2,z20,z6]),(0,[z31,z0,z521,z1,z2,z6]),(0,[z0,z1,z2,z20,z3,z830])],[(0,[z0,z1,z831,z3,z4,z6]),(0,[z0,z1,z2,z3,z832,z6]),(0,[z0,z2,z3,z4,z833,z6]),(0,[z675,z1,z2,z3,z42,z6]),(0,[z31,z0,z1,z2,z298,z6]),(0,[z0,z92,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z173]),(0,[z370,z0,z1,z266,z3,z6])],[(0,[z171,z0,z2,z212,z3,z6]),(0,[z0,z1,z834,z3,z4,z6]),(0,[z31,z0,z157,z1,z381,z6]),(0,[z0,z2,z339,z3,z4,z173]),(0,[z0,z1,z2,z20,z642,z6]),(0,[z31,z0,z1,z2,z6,z105])],[(0,[z0,z1,z2,z3,z4,z835]),(0,[z0,z1,z2,z3,z836,z6]),(0,[z0,z1,z2,z3,z4,z837]),(0,[z0,z838,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z839,z6]),(0,[z840,z1,z2,z3,z4,z6]),(0,[z841,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z842,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z843,z4]),(0,[z0,z1,z2,z289,z501,z6]),(0,[z0,z1,z2,z844,z4,z6]),(0,[z31,z0,z201,z2,z3,z6]),(0,[z0,z39,z812,z1,z2,z6]),(0,[z31,z0,z1,z2,z113,z6])],[(0,[z0,z845,z2,z3,z4,z6]),(0,[z0,z1,z2,z846,z3,z4]),(0,[z0,z183,z52,z1,z2,z6])],[(0,[z0,z144,z2,z40,z4,z6]),(0,[z0,z1,z2,z3,z847,z6]),(0,[z0,z1,z2,z3,z848,z6]),(0,[z0,z1,z2,z3,z849,z6]),(0,[z0,z1,z2,z143,z285,z4]),(0,[z31,z0,z1,z2,z54,z6]),(0,[z31,z0,z598,z1,z2,z6])],[(0,[z0,z850,z2,z3,z4,z6]),(0,[z0,z249,z1,z3,z112,z6]),(0,[z31,z0,z1,z2,z223,z6]),(0,[z0,z1,z2,z3,z851,z6]),(0,[z0,z1,z2,z4,z6,z852]),(0,[z0,z52,z2,z3,z853,z6]),(0,[z31,z0,z1,z2,z6,z123])],[(0,[z0,z1,z2,z3,z854,z6]),(0,[z0,z1,z2,z855,z3,z4]),(0,[z31,z0,z1,z2,z109,z6]),(0,[z43,z1,z2,z365,z44,z6]),(0,[z0,z1,z2,z3,z4,z856]),(0,[z0,z15,z2,z3,z4,z292]),(0,[z0,z1,z2,z3,z6,z857]),(0,[z31,z190,z1,z55,z2,z6]),(0,[z0,z858,z2,z3,z4,z6])],[(0,[z194,z1,z2,z3,z4,z65]),(0,[z0,z1,z2,z3,z4,z859]),(0,[z0,z92,z2,z3,z4,z64])],[(0,[z0,z860,z2,z3,z4,z6]),(0,[z0,z2,z3,z53,z6,z368]),(0,[z0,z729,z2,z20,z3,z6])],[(1,[z1,z861,z3,z4,z6]),(0,[z0,z639,z2,z3,z97,z6]),(0,[z0,z459,z111,z1,z2,z6]),(0,[z31,z0,z862,z1,z2,z3])]],
   [[(0,[z863,z0,z1,z2,z3,z6]),(0,[z31,z43,z1,z2,z8,z6]),(0,[z0,z85,z1,z2,z3,z309]),(0,[z0,z111,z1,z258,z112,z6])],[(0,[z0,z2,z3,z864,z4,z6]),(0,[z121,z1,z2,z109,z155,z6]),(0,[z0,z1,z2,z3,z132,z6])],[(0,[z0,z1,z2,z865,z3,z4]),(0,[z0,z1,z2,z3,z4,z866]),(0,[z31,z0,z108,z1,z2,z6]),(0,[z0,z1,z2,z365,z44,z6]),(0,[z0,z1,z2,z3,z4,z867]),(0,[z31,z0,z1,z2,z145,z6]),(0,[z31,z0,z415,z1,z2,z6]),(0,[z0,z122,z2,z3,z4,z771]),(0,[z0,z868,z2,z3,z4,z6]),(0,[z0,z869,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z360,z6]),(0,[z0,z1,z2,z3,z4,z830])],[(0,[z0,z2,z30,z3,z4,z293]),(0,[z0,z122,z2,z3,z4,z680]),(0,[z31,z0,z1,z2,z151,z6])],[(0,[z0,z870,z1,z2,z4,z6]),(1,[z0,z871,z3,z4,z6]),(0,[z872,z1,z2,z3,z4,z6]),(0,[z190,z1,z2,z20,z3,z6]),(0,[z0,z220,z2,z3,z205,z6])],[(0,[z0,z144,z2,z3,z4,z6]),(0,[z0,z1,z2,z873,z4,z6]),(0,[z0,z1,z2,z874,z3,z4]),(0,[z0,z92,z2,z4,z6,z282])],[(0,[z0,z222,z2,z3,z4,z167]),(0,[z0,z72,z871,z3,z4,z6]),(0,[z0,z15,z2,z20,z3,z160])],[(0,[z43,z1,z2,z270,z44,z6]),(0,[z35,z1,z2,z20,z3,z37]),(0,[z0,z1,z2,z3,z4,z73]),(0,[z31,z0,z103,z2,z30,z6]),(0,[z31,z0,z157,z1,z2,z6]),(0,[z875,z1,z2,z3,z4,z6]),(0,[z0,z1,z823,z3,z4,z6])]],
   [[(0,[z31,z0,z154,z1,z2,z6]),(0,[z0,z1,z2,z3,z4,z167]),(0,[z0,z1,z876,z2,z3,z4]),(0,[z31,z0,z39,z2,z78,z6]),(0,[z31,z0,z1,z2,z173,z6]),(0,[z31,z19,z1,z55,z2,z6]),(0,[z31,z0,z2,z3,z6,z117])],[(0,[z0,z1,z596,z3,z199,z6]),(0,[z0,z1,z2,z3,z877,z4]),(0,[z0,z355,z1,z2,z4,z6])],[(0,[z31,z0,z1,z2,z676,z6]),(0,[z171,z0,z201,z2,z3,z6]),(0,[z0,z2,z212,z3,z181,z6]),(0,[z0,z878,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z879,z6]),(0,[z880,z1,z2,z3,z4,z6]),(0,[z0,z15,z2,z3,z4,z328])],[(0,[z0,z1,z2,z3,z4,z881]),(0,[z0,z1,z2,z3,z882,z6]),(0,[z43,z171,z1,z2,z3,z6]),(0,[z0,z183,z1,z2,z184,z4]),(0,[z0,z1,z202,z2,z4,z216]),(0,[z0,z52,z2,z3,z205,z6]),(0,[z0,z1,z2,z883,z4,z6])],[(0,[z0,z1,z2,z3,z884,z6]),(0,[z121,z1,z2,z732,z4,z6]),(0,[z0,z1,z2,z3,z4,z885]),(0,[z0,z1,z886,z3,z4,z6]),(0,[z0,z887,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z56,z173]),(0,[z31,z0,z523,z1,z2,z6])],[(0,[z0,z1,z2,z3,z4,z888]),(0,[z31,z1,z2,z109,z8,z6]),(0,[z31,z0,z1,z2,z660,z6]),(0,[z0,z1,z2,z3,z4,z771]),(0,[z0,z122,z2,z20,z3,z79])],[(0,[z0,z144,z2,z3,z501,z6]),(0,[z0,z1,z2,z3,z56,z436]),(0,[z31,z0,z58,z1,z2,z137])],[(0,[z0,z222,z2,z20,z3,z6]),(0,[z0,z1,z2,z515,z20,z6]),(0,[z31,z0,z1,z2,z588,z6])]],
   [[(0,[z0,z1,z889,z3,z4,z6]),(0,[z0,z1,z2,z712,z8,z6]),(0,[z0,z58,z385,z1,z2,z137])],[(0,[z0,z1,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z890,z6]),(0,[z0,z1,z2,z3,z501,z167]),(0,[z1,z162,z3,z4,z6,z189]),(0,[z31,z0,z483,z1,z2,z6]),(0,[z31,z0,z157,z1,z266,z6]),(0,[z0,z891,z2,z3,z4,z6])],[(0,[z0,z222,z2,z40,z4,z6]),(0,[z0,z1,z2,z181,z270,z6]),(0,[z0,z1,z2,z3,z4,z793]),(1,[z31,z0,z17,z2,z6]),(0,[z0,z111,z1,z3,z734,z6]),(0,[z0,z71,z1,z3,z4,z64]),(0,[z31,z190,z1,z2,z492,z6]),(0,[z0,z1,z2,z113,z798,z6])],[(0,[z0,z1,z892,z2,z3,z4]),(0,[z194,z1,z2,z3,z4,z6]),(0,[z893,z0,z1,z2,z3,z6]),(0,[z0,z164,z2,z3,z4,z6]),(0,[z0,z81,z30,z20,z3,z6]),(0,[z1,z2,z3,z894,z4,z6]),(0,[z0,z14,z641,z3,z4,z6]),(0,[z31,z0,z183,z1,z2,z6]),(0,[z0,z67,z2,z3,z97,z6]),(0,[z0,z183,z67,z1,z2,z6]),(0,[z0,z1,z2,z3,z4,z895]),(0,[z0,z111,z1,z3,z112,z379]),(0,[z0,z1,z2,z3,z896,z6]),(0,[z0,z1,z2,z9,z896,z6]),(0,[z0,z2,z3,z4,z897,z6])],[(0,[z0,z898,z1,z2,z4,z6]),(0,[z0,z1,z2,z40,z4,z6]),(0,[z0,z1,z2,z3,z899,z6]),(0,[z1,z861,z93,z3,z4,z6]),(0,[z0,z1,z2,z365,z42,z6]),(0,[z0,z1,z2,z492,z365,z6]),(0,[z31,z0,z717,z2,z3,z6]),(0,[z0,z58,z133,z2,z3,z4])],[(0,[z0,z1,z2,z3,z900,z6]),(0,[z0,z1,z2,z3,z4,z49]),(0,[z0,z102,z212,z3,z4,z6]),(0,[z279,z1,z2,z8,z4,z6]),(0,[z1,z2,z3,z743,z4,z6]),(0,[z36,z1,z2,z20,z3,z65]),(0,[z0,z1,z2,z3,z901,z6]),(0,[z0,z15,z2,z3,z243,z4]),(0,[z0,z17,z2,z20,z3,z6]),(0,[z31,z0,z1,z24,z2,z6]),(0,[z0,z1,z2,z3,z4,z902]),(0,[z31,z0,z1,z2,z6,z208])],[(0,[z0,z1,z2,z4,z903,z6]),(0,[z31,z190,z1,z2,z8,z6]),(0,[z904,z1,z2,z3,z4,z6]),(0,[z0,z15,z2,z3,z4,z627])],[(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z1,z2,z3,z906,z6])]],
   [[(0,[z0,z144,z2,z289,z4,z6]),(0,[z0,z1,z2,z3,z4,z907]),(0,[z0,z1,z2,z143,z4,z105])],[(0,[z0,z2,z212,z3,z4,z6]),(0,[z0,z1,z908,z3,z4,z6]),(0,[z19,z1,z2,z109,z4,z6]),(0,[z909,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z771,z6]),(0,[z0,z359,z1,z3,z251,z6])],[(0,[z0,z1,z910,z2,z3,z4]),(0,[z0,z1,z2,z3,z911,z6]),(0,[z31,z0,z102,z1,z3,z6]),(0,[z31,z0,z1,z2,z693,z6]),(0,[z0,z21,z2,z3,z97,z6]),(1,[z0,z1,z768,z4,z6]),(0,[z0,z1,z3,z4,z734,z6]),(0,[z0,z1,z2,z3,z86,z735])],[(0,[z721,z127,z2,z3,z4,z6]),(0,[z0,z1,z2,z289,z4,z167]),(0,[z23,z31,z0,z157,z1,z6]),(0,[z0,z201,z2,z241,z3,z4])],[(0,[z0,z1,z2,z3,z912,z6]),(0,[z0,z1,z2,z913,z3,z6]),(0,[z36,z1,z2,z3,z4,z867]),(0,[z31,z0,z15,z2,z3,z160])],[(0,[z31,z35,z0,z58,z1,z2]),(0,[z0,z914,z1,z2,z3,z6]),(0,[z0,z2,z871,z3,z4,z6]),(0,[z0,z1,z2,z3,z915,z6]),(0,[z0,z1,z2,z3,z4,z916]),(0,[z0,z1,z2,z3,z333,z118])],[(0,[z0,z1,z2,z917,z4,z6]),(0,[z0,z1,z2,z3,z501,z49]),(0,[z0,z1,z2,z3,z918,z6]),(0,[z0,z919,z1,z2,z3,z6]),(0,[z31,z0,z1,z920,z3,z6])],[(0,[z0,z657,z30,z3,z4,z6]),(0,[z0,z921,z2,z3,z4,z6]),(0,[z0,z2,z241,z212,z3,z4]),(0,[z0,z1,z27,z20,z3,z6]),(0,[z31,z0,z1,z2,z482,z3])]],
   [[(0,[z31,z0,z269,z1,z2,z4]),(0,[z0,z2,z922,z3,z4,z6]),(0,[z0,z1,z2,z3,z923,z6]),(0,[z0,z1,z2,z3,z119,z622]),(0,[z0,z2,z3,z4,z6,z924]),(0,[z150,z0,z321,z2,z3,z6])],[(0,[z0,z2,z3,z4,z925,z6]),(0,[z0,z1,z2,z365,z4,z6]),(0,[z1,z2,z3,z44,z743,z6]),(1,[z1,z2,z3,z4,z867]),(0,[z0,z81,z30,z3,z4,z6]),(0,[z31,z0,z81,z30,z3,z6]),(0,[z0,z459,z1,z2,z20,z6]),(0,[z0,z210,z1,z3,z4,z64])],[(0,[z297,z127,z2,z3,z4,z6]),(0,[z926,z0,z1,z2,z3,z6]),(0,[z36,z1,z2,z3,z4,z167]),(0,[z31,z19,z1,z2,z8,z6]),(0,[z0,z303,z2,z3,z4,z6]),(1,[z0,z2,z790,z4,z6]),(0,[z0,z1,z2,z3,z853,z6]),(0,[z0,z157,z221,z1,z104,z6]),(0,[z0,z2,z339,z3,z99,z6]),(0,[z31,z0,z1,z55,z32,z6]),(0,[z0,z2,z927,z3,z4,z6]),(0,[z0,z355,z85,z1,z2,z6])],[(0,[z59,z721,z2,z3,z4,z6]),(0,[z0,z1,z861,z3,z4,z6]),(0,[z0,z1,z2,z928,z3,z4]),(0,[z43,z1,z2,z3,z155,z6]),(0,[z0,z1,z2,z3,z6,z929]),(0,[z0,z930,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z931,z6]),(0,[z0,z103,z261,z2,z129,z6]),(0,[z0,z932,z1,z2,z4,z6])],[(0,[z23,z1,z683,z3,z4,z6]),(0,[z31,z0,z1,z186,z2,z6]),(0,[z31,z0,z435,z1,z2,z6])],[(0,[z0,z933,z1,z2,z3,z4]),(0,[z0,z1,z2,z934,z3,z4]),(0,[z60,z222,z2,z3,z4,z6]),(0,[z31,z0,z102,z1,z2,z6]),(0,[z802,z1,z2,z3,z4,z6])],[(0,[z31,z0,z269,z1,z2,z8]),(0,[z0,z1,z2,z3,z935,z6]),(0,[z0,z341,z2,z78,z3,z4]),(0,[z0,z1,z2,z3,z99,z436]),(0,[z0,z111,z164,z3,z112,z6])],[(0,[z0,z1,z2,z936,z3,z6]),(0,[z0,z1,z2,z3,z6,z937]),(0,[z0,z1,z2,z3,z938,z6]),(0,[z297,z1,z2,z20,z3,z6]),(0,[z1,z2,z939,z3,z4,z6]),(0,[z0,z940,z1,z2,z3,z6]),(0,[z0,z261,z1,z341,z2,z3]),(0,[z0,z1,z2,z3,z4,z941]),(0,[z0,z1,z2,z3,z4,z173]),(0,[z0,z1,z2,z9,z4,z173]),(0,[z31,z190,z58,z1,z2,z6]),(0,[z31,z0,z2,z3,z6,z278]),(0,[z0,z1,z2,z114,z20,z6])]],
   [[(0,[z59,z60,z2,z20,z3,z6]),(0,[z0,z1,z2,z289,z4,z49]),(0,[z31,z0,z103,z15,z2,z6]),(0,[z0,z2,z20,z3,z6,z278]),(0,[z0,z385,z133,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z942]),(0,[z0,z943,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z155,z6]),(0,[z43,z1,z2,z3,z314,z6]),(0,[z1,z2,z944,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z945]),(0,[z599,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z3,z946,z6]),(0,[z0,z947,z2,z3,z4,z6])],[(0,[z31,z0,z1,z2,z686,z6]),(0,[z0,z221,z1,z2,z109,z6]),(0,[z0,z1,z2,z3,z83,z6]),(0,[z0,z1,z2,z9,z83,z6]),(0,[z0,z1,z2,z184,z4,z216]),(0,[z0,z17,z2,z3,z4,z173]),(1,[z31,z0,z1,z2,z173]),(0,[z0,z355,z2,z4,z6,z117])],[(0,[z171,z0,z102,z1,z3,z6]),(0,[z0,z1,z2,z270,z4,z6]),(0,[z31,z0,z103,z321,z2,z6]),(0,[z31,z0,z1,z2,z336,z6])],[(0,[z0,z102,z1,z241,z3,z4]),(0,[z19,z1,z2,z365,z4,z6]),(0,[z0,z1,z948,z3,z4,z6]),(0,[z31,z0,z103,z2,z129,z6]),(0,[z0,z1,z55,z32,z4,z6]),(0,[z31,z0,z17,z1,z2,z6]),(1,[z0,z1,z3,z734,z6])],[(0,[z7,z201,z2,z8,z4,z6]),(0,[z7,z269,z1,z2,z8,z4]),(0,[z31,z0,z55,z2,z339,z6])],[(0,[z0,z1,z949,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z950]),(0,[z0,z39,z2,z78,z20,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z951]),(0,[z31,z0,z411,z1,z2,z6]),(0,[z0,z122,z2,z3,z4,z556])],[(0,[z0,z1,z2,z3,z4,z952]),(0,[z0,z144,z2,z3,z4,z167]),(1,[z31,z0,z201,z2,z6]),(0,[z0,z953,z2,z3,z4,z6]),(0,[z0,z17,z55,z32,z4,z6])],[(0,[z0,z1,z2,z3,z954,z6]),(0,[z0,z1,z955,z3,z4,z6]),(0,[z0,z1,z2,z3,z956,z6]),(0,[z0,z1,z2,z3,z957,z6]),(0,[z31,z0,z359,z1,z2,z6]),(0,[z0,z1,z2,z20,z3,z859])],[(0,[z297,z222,z2,z3,z4,z6]),(0,[z0,z220,z183,z1,z2,z6]),(0,[z31,z0,z459,z1,z2,z6]),(0,[z31,z0,z1,z2,z500,z6])],[(0,[z0,z958,z2,z3,z4,z6]),(0,[z0,z959,z1,z2,z3,z6]),(0,[z0,z1,z341,z2,z3,z374]),(0,[z0,z1,z2,z20,z3,z184]),(0,[z31,z0,z1,z2,z56,z6]),(0,[z31,z0,z1,z2,z3,z417])],[(0,[z7,z1,z2,z181,z8,z6]),(0,[z0,z1,z2,z4,z960,z6]),(0,[z0,z1,z2,z3,z4,z961]),(0,[z0,z1,z2,z3,z6,z462]),(0,[z0,z1,z2,z9,z6,z462]),(0,[z0,z962,z2,z3,z4,z6]),(0,[z0,z2,z4,z6,z117,z282])],[(0,[z1,z2,z3,z4,z6,z90]),(0,[z0,z1,z2,z4,z216,z6]),(0,[z31,z0,z1,z2,z68,z6]),(0,[z31,z875,z1,z2,z3,z6])],[(0,[z297,z81,z30,z3,z4,z6]),(0,[z297,z103,z2,z3,z4,z6]),(0,[z0,z1,z2,z963,z4,z6]),(0,[z31,z0,z1,z55,z2,z6]),(0,[z0,z1,z2,z964,z4,z6])]],
   [[(0,[z0,z965,z2,z3,z4,z6])],[(0,[z1,z2,z365,z8,z4,z6]),(0,[z31,z19,z1,z2,z365,z6]),(0,[z0,z1,z2,z4,z896,z6]),(0,[z31,z0,z1,z2,z6,z282]),(0,[z0,z1,z2,z3,z6,z281]),(0,[z0,z85,z1,z2,z3,z118]),(0,[z0,z966,z2,z3,z4,z6])],[(0,[z0,z144,z2,z20,z3,z6]),(0,[z0,z1,z2,z967,z3,z6]),(0,[z31,z0,z1,z2,z3,z436]),(0,[z0,z355,z1,z2,z4,z91])],[(0,[z0,z1,z2,z3,z968,z6]),(0,[z0,z2,z969,z3,z4,z6]),(0,[z1,z2,z3,z970,z4,z6]),(0,[z0,z103,z2,z338,z4,z6]),(0,[z0,z15,z177,z2,z3,z4]),(0,[z0,z2,z339,z3,z4,z436]),(0,[z0,z1,z131,z3,z251,z6]),(0,[z31,z0,z322,z1,z2,z6])],[(0,[z1,z2,z861,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z73])],[(0,[z0,z1,z2,z3,z971,z6]),(0,[z23,z1,z93,z3,z4,z6]),(0,[z0,z1,z2,z20,z3,z167]),(0,[z0,z102,z1,z32,z4,z6]),(0,[z0,z1,z2,z4,z972,z6]),(0,[z0,z1,z2,z3,z973,z6]),(0,[z0,z1,z2,z20,z258,z6]),(0,[z0,z1,z3,z4,z64,z902])],[(0,[z1,z721,z2,z3,z4,z6]),(0,[z31,z59,z60,z2,z3,z6]),(0,[z0,z144,z2,z3,z4,z49]),(0,[z0,z1,z2,z974,z4,z6]),(0,[z1,z2,z3,z4,z37,z696]),(0,[z31,z0,z1,z2,z96,z6]),(0,[z0,z39,z2,z78,z83,z6])],[(0,[z0,z1,z2,z3,z975,z6]),(0,[z194,z1,z2,z3,z4,z167]),(0,[z31,z7,z1,z2,z8,z6]),(0,[z0,z976,z1,z2,z3,z6]),(0,[z0,z103,z2,z129,z4,z6]),(0,[z0,z103,z321,z2,z4,z6]),(0,[z0,z2,z78,z4,z6,z123]),(0,[z0,z2,z3,z4,z853,z6]),(0,[z0,z2,z3,z4,z6,z977]),(0,[z0,z978,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z119,z86])]],
   [[(0,[z0,z1,z2,z40,z4,z167]),(0,[z7,z102,z1,z8,z4,z6]),(0,[z19,z1,z2,z8,z4,z6]),(0,[z31,z0,z1,z2,z181,z6]),(0,[z31,z0,z1,z2,z3,z293]),(0,[z31,z0,z1,z2,z3,z979]),(0,[z31,z0,z1,z2,z332,z6])],[(0,[z0,z1,z2,z3,z980,z6]),(0,[z0,z1,z2,z20,z289,z6]),(0,[z0,z1,z2,z3,z184,z4]),(0,[z31,z0,z1,z2,z333,z6]),(0,[z31,z981,z1,z2,z3,z6])],[(0,[z31,z0,z1,z317,z2,z6]),(0,[z209,z0,z1,z381,z3,z6])],[(0,[z0,z2,z3,z4,z771,z160]),(0,[z0,z111,z235,z3,z112,z6]),(0,[z0,z71,z1,z3,z4,z902])],[(0,[z982,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z983]),(0,[z0,z67,z202,z2,z3,z4]),(0,[z0,z1,z2,z3,z984,z6]),(0,[z0,z985,z2,z20,z3,z6])],[(0,[z0,z1,z986,z2,z3,z4]),(0,[z31,z0,z18,z1,z2,z6]),(0,[z0,z355,z92,z2,z4,z6])],[(0,[z23,z1,z93,z3,z501,z6]),(0,[z195,z1,z628,z3,z4,z6]),(0,[z81,z29,z30,z3,z4,z6]),(0,[z0,z14,z202,z2,z3,z4]),(0,[z0,z1,z987,z3,z4,z6]),(0,[z0,z2,z3,z790,z4,z6]),(0,[z0,z1,z2,z3,z4,z988])],[(0,[z31,z0,z1,z2,z487,z6]),(0,[z0,z1,z2,z3,z989,z6]),(0,[z0,z71,z1,z20,z3,z64]),(0,[z0,z21,z2,z558,z3,z6])]],
   [[(0,[z62,z127,z2,z3,z4,z6]),(0,[z0,z1,z2,z990,z4,z6]),(0,[z31,z0,z1,z2,z545,z6]),(0,[z0,z164,z2,z20,z3,z6]),(0,[z194,z1,z2,z20,z3,z6])],[(0,[z0,z1,z2,z3,z991,z4]),(0,[z0,z355,z1,z2,z20,z6])],[(0,[z0,z1,z2,z20,z3,z49])],[(0,[z0,z1,z2,z3,z992,z6]),(0,[z0,z102,z269,z1,z3,z4]),(0,[z1,z2,z3,z743,z42,z6]),(0,[z0,z1,z2,z993,z4,z6]),(0,[z994,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z809])],[(0,[z1,z162,z166,z3,z4,z6]),(0,[z0,z1,z2,z20,z12,z6]),(0,[z0,z1,z2,z3,z995,z6]),(0,[z31,z0,z103,z14,z2,z6]),(0,[z0,z67,z2,z3,z853,z6]),(0,[z0,z67,z2,z3,z184,z97]),(0,[z0,z2,z20,z3,z6,z117])],[(0,[z0,z1,z2,z40,z4,z49]),(0,[z31,z0,z1,z2,z492,z6]),(0,[z0,z2,z339,z3,z56,z6]),(0,[z0,z1,z2,z3,z735,z118])],[(0,[z0,z1,z2,z996,z4,z6]),(0,[z0,z2,z212,z20,z3,z6]),(0,[z1,z2,z3,z4,z997,z6]),(0,[z31,z0,z103,z39,z2,z6]),(0,[z31,z0,z71,z1,z3,z64]),(0,[z31,z0,z819,z2,z3,z6]),(0,[z0,z385,z1,z2,z3,z6])],[(0,[z194,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z998,z4,z6])]],
   [[(0,[z1,z2,z29,z3,z4,z6]),(0,[z23,z1,z93,z289,z4,z6]),(0,[z31,z0,z1,z2,z373,z6]),(0,[z0,z39,z2,z790,z4,z6]),(0,[z1,z2,z3,z999,z4,z6]),(0,[z31,z0,z58,z1,z2,z91]),(0,[z0,z1,z2,z143,z11,z113])],[(0,[z0,z1000,z1,z2,z3,z6]),(0,[z31,z0,z1,z2,z8,z6]),(0,[z0,z183,z2,z30,z4,z6]),(0,[z31,z0,z1,z224,z2,z6])],[(0,[z31,z0,z1,z2,z540,z6]),(0,[z0,z213,z2,z3,z4,z79]),(0,[z0,z235,z2,z3,z4,z417]),(0,[z0,z1,z2,z20,z3,z916]),(0,[z0,z985,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1001,z4,z6]),(0,[z1002,z0,z1,z2,z3,z6]),(0,[z0,z2,z3,z4,z79,z771]),(0,[z0,z303,z2,z3,z4,z91]),(0,[z0,z2,z3,z4,z807,z6])],[(0,[z0,z1,z2,z3,z1003,z4]),(0,[z31,z0,z1,z2,z241,z8]),(0,[z1,z2,z3,z155,z42,z6]),(0,[z0,z1004,z1,z2,z3,z6]),(0,[z0,z521,z15,z2,z3,z4]),(0,[z0,z355,z1,z2,z4,z64]),(0,[z31,z190,z1,z2,z20,z6])],[(0,[z0,z1,z2,z3,z4,z1005]),(0,[z0,z1006,z2,z3,z4,z6]),(0,[z0,z1,z2,z482,z3,z374]),(0,[z31,z0,z1,z2,z285,z6])],[(0,[z0,z222,z2,z3,z4,z49]),(0,[z0,z75,z2,z3,z4,z6]),(0,[z0,z183,z14,z2,z4,z6]),(0,[z1,z2,z3,z4,z6,z1007]),(0,[z31,z0,z17,z55,z2,z6]),(0,[z31,z0,z1,z2,z798,z6])],[(0,[z0,z201,z2,z3,z181,z6]),(0,[z0,z303,z2,z20,z3,z6]),(0,[z0,z355,z1,z2,z86,z6])]],
   [[(0,[z31,z0,z1,z2,z393,z6]),(0,[z0,z55,z339,z32,z4,z6]),(0,[z0,z71,z75,z3,z4,z64]),(0,[z0,z1,z2,z20,z9,z6]),(0,[z0,z1,z2,z3,z6,z735])],[(0,[z62,z222,z2,z3,z4,z6]),(0,[z0,z1,z2,z143,z268,z4])],[(0,[z0,z269,z1,z2,z3,z4]),(0,[z0,z1,z2,z109,z155,z6]),(0,[z31,z0,z1,z2,z396,z6]),(0,[z0,z1,z2,z3,z4,z1008]),(0,[z31,z0,z677,z1,z2,z6]),(0,[z0,z1,z2,z3,z86,z179])],[(0,[z0,z1,z1009,z3,z4,z6]),(0,[z0,z1,z2,z3,z1010,z6]),(0,[z0,z14,z2,z3,z4,z293]),(0,[z0,z261,z1,z2,z482,z3]),(0,[z31,z0,z1,z2,z400,z6])],[(0,[z0,z1,z2,z3,z4,z1011]),(0,[z31,z0,z201,z1,z2,z6]),(0,[z797,z1,z2,z3,z4,z6]),(0,[z31,z0,z593,z1,z2,z6]),(0,[z0,z1,z2,z20,z3,z173]),(0,[z31,z0,z334,z1,z2,z6]),(0,[z981,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1012,z40,z6]),(0,[z31,z121,z1,z2,z109,z6]),(0,[z31,z0,z1,z2,z295,z6]),(0,[z0,z14,z871,z3,z4,z6]),(0,[z0,z14,z72,z3,z4,z73]),(0,[z0,z1,z202,z2,z3,z4]),(0,[z0,z1013,z1,z2,z3,z6]),(0,[z31,z0,z1,z2,z629,z6])],[(0,[z0,z1,z2,z3,z4,z1014]),(0,[z31,z0,z1,z2,z700,z6]),(0,[z0,z1,z2,z1015,z4,z6]),(0,[z0,z1,z647,z3,z112,z6])],[(0,[z31,z0,z1,z2,z408,z6]),(0,[z1,z2,z3,z4,z37,z867]),(0,[z31,z0,z1,z2,z314,z6])]],
   [[(0,[z0,z1,z2,z1016,z4,z6]),(0,[z0,z1017,z2,z3,z4,z6]),(1,[z31,z0,z269,z1,z2]),(0,[z31,z35,z1,z2,z3,z37]),(0,[z0,z1,z2,z20,z494,z6]),(0,[z1018,z1,z2,z3,z4,z6]),(0,[z31,z19,z1,z2,z20,z6]),(0,[z0,z85,z92,z2,z3,z4])],[(0,[z0,z14,z557,z3,z4,z6]),(0,[z0,z1,z2,z365,z20,z6]),(0,[z0,z2,z3,z853,z97,z6]),(0,[z31,z0,z1,z202,z2,z3]),(0,[z0,z1,z3,z4,z902,z6])],[(0,[z0,z1,z2,z3,z4,z1019]),(0,[z171,z0,z269,z1,z2,z3]),(0,[z0,z1,z2,z3,z1020,z6]),(0,[z0,z157,z1,z768,z4,z6]),(0,[z0,z1,z55,z768,z4,z6]),(0,[z0,z1,z55,z4,z252,z6]),(0,[z0,z1,z2,z3,z1021,z6]),(0,[z31,z0,z1,z2,z149,z6]),(0,[z31,z0,z58,z1,z2,z6]),(0,[z31,z0,z1022,z2,z3,z6]),(0,[z0,z58,z1,z2,z4,z809])],[(0,[z0,z1,z2,z3,z4,z1023]),(0,[z0,z1024,z2,z3,z4,z6]),(0,[z31,z0,z103,z2,z79,z6])],[(0,[z0,z1025,z1,z3,z4,z6]),(0,[z1026,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z592,z20,z6]),(0,[z1027,z0,z1,z2,z3,z6]),(0,[z0,z58,z1,z2,z4,z554]),(1,[z0,z1,z2,z896,z6]),(0,[z0,z58,z385,z1,z2,z6])],[(0,[z1,z2,z3,z4,z37,z167]),(0,[z7,z1,z2,z241,z8,z4]),(0,[z329,z1,z2,z8,z4,z6]),(0,[z121,z1,z2,z109,z140,z6]),(0,[z0,z1,z2,z4,z6,z1028]),(0,[z31,z0,z1,z647,z2,z6]),(0,[z46,z0,z1,z2,z3,z554]),(0,[z0,z1,z647,z344,z3,z6])],[(0,[z0,z201,z2,z3,z4,z6]),(0,[z23,z144,z93,z3,z4,z6]),(0,[z0,z201,z2,z9,z4,z6]),(0,[z31,z0,z667,z1,z2,z6]),(0,[z0,z221,z1,z55,z2,z6]),(0,[z0,z1,z2,z3,z4,z417]),(0,[z31,z190,z1,z2,z10,z6])],[(1,[z721,z2,z3,z4,z6]),(0,[z1,z162,z861,z3,z4,z6]),(0,[z31,z0,z324,z1,z2,z6]),(0,[z0,z14,z72,z20,z3,z6]),(0,[z0,z15,z2,z3,z4,z265]),(0,[z0,z1,z2,z4,z809,z137])]],
   [[(0,[z31,z1,z2,z8,z42,z6]),(0,[z31,z0,z1,z2,z365,z6]),(0,[z0,z67,z202,z2,z3,z97]),(0,[z31,z0,z1,z948,z3,z6]),(0,[z427,z1,z2,z3,z314,z6]),(0,[z0,z1,z2,z4,z113,z809])],[(0,[z23,z1,z93,z3,z4,z167]),(0,[z0,z102,z1,z3,z181,z6]),(0,[z0,z1,z2,z3,z1029,z6]),(0,[z31,z36,z1,z2,z3,z65]),(0,[z0,z1030,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z1031]),(0,[z31,z0,z1,z51,z2,z6]),(0,[z0,z111,z1,z3,z112,z6]),(0,[z31,z0,z1,z2,z597,z6])],[(0,[z0,z1,z2,z967,z289,z6]),(0,[z0,z1,z2,z3,z4,z1032]),(0,[z0,z58,z1,z2,z338,z4]),(0,[z0,z1,z2,z3,z1033,z6]),(0,[z31,z0,z157,z1,z104,z6]),(0,[z0,z2,z3,z4,z6,z1034]),(0,[z1,z2,z3,z4,z6,z1035]),(0,[z31,z0,z58,z1,z2,z64])],[(0,[z0,z1,z2,z1036,z4,z6]),(0,[z43,z190,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1037,z6]),(0,[z0,z1,z2,z3,z374,z6]),(0,[z0,z2,z3,z4,z79,z255]),(0,[z0,z1,z2,z896,z10,z6])],[(0,[z23,z1,z861,z3,z4,z6]),(0,[z31,z0,z1,z27,z8,z6]),(0,[z0,z1,z2,z3,z4,z436])],[(0,[z31,z190,z39,z1,z2,z6]),(0,[z0,z1,z32,z768,z4,z6]),(0,[z0,z303,z2,z3,z4,z64])],[(0,[z0,z1,z2,z3,z4,z1038]),(0,[z0,z1,z2,z3,z1039,z6]),(0,[z0,z1,z2,z4,z6,z1040]),(0,[z31,z0,z17,z2,z4,z6]),(0,[z0,z58,z133,z2,z4,z137])],[(0,[z0,z1041,z2,z3,z4,z6]),(0,[z31,z190,z1,z2,z3,z6]),(0,[z31,z0,z58,z1,z2,z176])]],
   [[(0,[z0,z1,z3,z4,z6,z1042]),(0,[z0,z17,z2,z3,z4,z436]),(0,[z31,z909,z1,z2,z3,z6])],[(0,[z31,z0,z594,z1,z2,z6]),(0,[z297,z60,z2,z3,z4,z6]),(0,[z0,z1,z2,z1043,z4,z6]),(0,[z0,z355,z85,z1,z2,z118])],[(0,[z0,z1,z2,z3,z1044,z6]),(0,[z0,z1,z2,z40,z76,z6]),(0,[z31,z0,z1,z2,z40,z6]),(0,[z23,z1,z93,z20,z3,z6]),(0,[z0,z1,z2,z3,z4,z293]),(0,[z0,z1,z2,z3,z1045,z6]),(0,[z0,z1,z2,z3,z4,z1046]),(0,[z0,z1,z202,z2,z20,z3]),(0,[z0,z1,z2,z3,z4,z979]),(0,[z0,z235,z2,z3,z4,z379]),(0,[z190,z1,z2,z266,z3,z6]),(0,[z31,z19,z1,z2,z10,z6])],[(0,[z0,z1047,z1,z2,z3,z6]),(0,[z0,z103,z2,z482,z129,z4]),(0,[z0,z39,z2,z4,z640,z6]),(0,[z0,z2,z3,z4,z6,z117]),(0,[z0,z1,z2,z3,z4,z1048]),(0,[z0,z1,z2,z143,z113,z462])],[(0,[z0,z1049,z2,z3,z4,z6]),(0,[z0,z201,z27,z3,z4,z6]),(0,[z0,z1050,z2,z3,z4,z6]),(0,[z31,z0,z260,z1,z2,z6]),(0,[z0,z1,z2,z1051,z4,z6])],[(0,[z23,z1,z93,z40,z4,z6]),(0,[z31,z195,z0,z157,z1,z6]),(0,[z0,z269,z1,z27,z3,z4]),(0,[z0,z14,z72,z3,z4,z6]),(0,[z0,z14,z525,z3,z4,z6]),(0,[z31,z0,z303,z2,z3,z6]),(0,[z31,z0,z1,z987,z3,z6])],[(0,[z23,z1,z93,z3,z4,z49]),(0,[z35,z1,z2,z124,z3,z4])],[(0,[z0,z1,z2,z3,z1052,z6]),(0,[z0,z1,z2,z1053,z3,z4]),(0,[z0,z399,z15,z2,z3,z4]),(0,[z0,z1,z2,z143,z4,z809])]],
   [[(0,[z31,z62,z127,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z1054]),(0,[z0,z102,z1,z3,z4,z6]),(0,[z0,z1055,z2,z3,z4,z6]),(0,[z0,z102,z1,z9,z4,z6]),(0,[z1,z2,z109,z732,z4,z6]),(0,[z0,z1,z55,z32,z4,z173]),(0,[z0,z1,z2,z3,z1056,z6]),(0,[z190,z1,z2,z3,z199,z6]),(0,[z209,z190,z1,z2,z3,z6])],[(0,[z0,z1,z1057,z3,z4,z6]),(0,[z1,z2,z3,z4,z867,z65]),(0,[z0,z1,z2,z1058,z4,z6]),(0,[z0,z1,z2,z3,z4,z1059]),(0,[z0,z133,z2,z3,z4,z6]),(0,[z31,z19,z39,z1,z2,z6]),(0,[z31,z1060,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1061,z6])],[(0,[z0,z1,z1062,z3,z4,z6]),(0,[z0,z1,z2,z3,z1063,z6]),(0,[z0,z222,z2,z3,z76,z6]),(0,[z0,z1,z2,z4,z6,z1064]),(0,[z0,z459,z1,z131,z2,z6]),(0,[z31,z19,z1,z2,z3,z6]),(0,[z0,z1,z2,z20,z3,z988])],[(0,[z1065,z0,z1,z2,z40,z6]),(0,[z0,z1,z2,z3,z4,z1066]),(0,[z349,z190,z1,z2,z3,z6]),(0,[z0,z1067,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1068,z4,z6]),(0,[z62,z127,z2,z20,z3,z6]),(0,[z0,z1,z2,z3,z76,z6]),(0,[z0,z1069,z2,z3,z4,z6]),(0,[z1070,z0,z1,z2,z3,z6]),(0,[z19,z190,z1,z2,z3,z6]),(0,[z31,z0,z577,z1,z2,z6])],[(0,[z23,z222,z93,z3,z4,z6]),(0,[z31,z0,z1,z2,z241,z3]),(0,[z1071,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z113,z444])],[(0,[z0,z1,z2,z1072,z4,z6]),(0,[z0,z871,z30,z3,z4,z6]),(0,[z0,z67,z321,z2,z3,z6]),(0,[z0,z1073,z2,z3,z4,z6])]],
   [[(0,[z0,z221,z1,z2,z8,z6]),(0,[z414,z0,z301,z2,z3,z6])],[(0,[z0,z1074,z2,z3,z4,z6]),(0,[z0,z1,z2,z8,z155,z6]),(0,[z171,z190,z1,z2,z3,z6]),(0,[z0,z1,z1075,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1076,z6]),(0,[z0,z1077,z2,z3,z4,z6]),(0,[z31,z0,z276,z1,z2,z6]),(0,[z31,z0,z1,z55,z2,z173]),(0,[z1,z89,z3,z4,z90,z91]),(0,[z0,z1,z2,z20,z6,z228])],[(0,[z0,z1,z3,z4,z1078,z6]),(0,[z297,z2,z78,z3,z4,z6]),(0,[z31,z0,z1,z2,z216,z6]),(0,[z0,z1,z55,z747,z2,z6])],[(1,[z1,z2,z732,z4,z6]),(0,[z0,z1079,z1,z2,z3,z4]),(0,[z31,z0,z235,z2,z3,z6]),(0,[z31,z0,z133,z2,z3,z6]),(0,[z0,z1080,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z6,z1081]),(0,[z1,z2,z29,z20,z3,z6]),(0,[z0,z235,z2,z3,z4,z6])],[(0,[z0,z1082,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1083]),(0,[z19,z1,z2,z3,z44,z6]),(0,[z0,z1,z2,z3,z1084,z6]),(0,[z0,z1,z2,z3,z4,z379]),(0,[z0,z862,z1,z2,z3,z4]),(0,[z31,z0,z1,z2,z896,z6])],[(0,[z31,z1,z2,z29,z3,z6]),(0,[z31,z19,z103,z1,z2,z6]),(0,[z233,z19,z1,z2,z3,z6])]],
   [[(0,[z0,z1085,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1086]),(0,[z0,z183,z1,z202,z2,z4]),(0,[z0,z2,z3,z53,z853,z6]),(0,[z0,z1087,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z1088]),(0,[z0,z1,z2,z143,z4,z113])],[(0,[z31,z0,z1,z2,z520,z6]),(0,[z0,z1,z2,z3,z4,z1089]),(0,[z0,z1090,z1,z2,z3,z6]),(0,[z0,z85,z1,z2,z282,z118])],[(0,[z41,z1,z2,z3,z743,z6]),(0,[z31,z0,z1,z2,z3,z1059])],[(0,[z0,z721,z2,z3,z4,z6]),(0,[z1091,z0,z1,z2,z3,z6]),(0,[z0,z212,z27,z3,z4,z6]),(0,[z31,z0,z2,z212,z8,z6]),(0,[z0,z103,z2,z374,z129,z6]),(0,[z31,z0,z1,z2,z518,z6]),(0,[z0,z75,z2,z20,z3,z6]),(0,[z0,z559,z355,z1,z2,z6])],[(0,[z0,z1092,z2,z3,z4,z6]),(0,[z0,z1093,z2,z3,z4,z6]),(0,[z0,z1,z3,z734,z112,z6]),(0,[z0,z1094,z2,z3,z4,z6]),(0,[z0,z1095,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1096,z4,z6]),(0,[z0,z1,z2,z3,z140,z6])],[(0,[z434,z60,z2,z3,z4,z6]),(0,[z41,z190,z1,z2,z3,z6]),(0,[z0,z81,z871,z3,z4,z6]),(0,[z0,z1,z2,z3,z119,z735])],[(0,[z31,z0,z222,z2,z3,z6]),(0,[z1097,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z1098,z4,z6]),(0,[z1,z2,z3,z4,z867,z6]),(0,[z0,z1,z2,z3,z4,z1099]),(0,[z0,z2,z3,z4,z79,z159]),(0,[z1100,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z20,z6]),(0,[z31,z0,z21,z1,z2,z6])]],
   [[(0,[z0,z1,z2,z289,z76,z6]),(0,[z0,z1,z2,z1101,z4,z6]),(0,[z171,z0,z1,z2,z241,z3]),(0,[z0,z1102,z2,z3,z4,z6]),(0,[z0,z808,z2,z3,z4,z6])],[(0,[z0,z1,z2,z241,z3,z4]),(0,[z0,z122,z2,z3,z512,z4]),(0,[z0,z1,z3,z199,z734,z6])],[(0,[z0,z1,z2,z3,z1103,z6]),(0,[z0,z1104,z2,z3,z4,z6]),(0,[z0,z1,z2,z790,z4,z6]),(0,[z0,z2,z3,z4,z6,z278]),(0,[z1060,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1105]),(0,[z0,z1,z89,z3,z4,z91]),(0,[z0,z1,z3,z4,z902,z91])],[(0,[z0,z1,z2,z3,z1106,z6]),(0,[z31,z0,z269,z1,z2,z3]),(0,[z1107,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z395,z6])],[(0,[z0,z1108,z1,z2,z4,z6]),(0,[z0,z201,z269,z2,z3,z4]),(0,[z0,z269,z2,z212,z3,z4]),(0,[z0,z1,z2,z3,z4,z1109]),(0,[z0,z103,z2,z790,z4,z6]),(0,[z0,z58,z1,z2,z4,z137])],[(0,[z0,z1,z2,z1012,z3,z6]),(0,[z0,z103,z341,z2,z129,z4]),(0,[z0,z1,z2,z4,z6,z1110]),(0,[z31,z0,z1,z2,z496,z6]),(0,[z31,z0,z1,z2,z143,z113])],[(0,[z195,z1,z162,z3,z4,z6]),(0,[z0,z1,z2,z482,z3,z4]),(0,[z0,z1,z2,z3,z99,z6]),(0,[z0,z1,z224,z3,z4,z64])],[(0,[z0,z1,z2,z1111,z4,z6]),(0,[z31,z0,z506,z1,z2,z6]),(0,[z0,z1112,z2,z3,z4,z6]),(0,[z284,z1,z2,z8,z4,z6]),(0,[z31,z0,z1,z2,z3,z379])]],
   [[(0,[z0,z1,z2,z1113,z4,z6])],[(0,[z1,z2,z732,z8,z4,z6]),(0,[z0,z1114,z2,z3,z4,z6]),(0,[z0,z1,z2,z1115,z4,z6]),(0,[z31,z0,z422,z1,z2,z6]),(0,[z0,z1,z2,z3,z4,z809])],[(0,[z31,z59,z0,z103,z2,z6]),(0,[z31,z0,z1,z170,z2,z6]),(0,[z0,z2,z693,z78,z4,z6]),(0,[z0,z1,z2,z3,z1116,z6]),(0,[z0,z17,z2,z3,z99,z6]),(0,[z0,z1,z2,z3,z1117,z6]),(0,[z31,z0,z1,z2,z4,z173]),(0,[z0,z1,z89,z3,z4,z902]),(0,[z0,z1,z2,z47,z3,z333]),(0,[z0,z58,z1,z2,z281,z137])],[(0,[z0,z1,z2,z3,z1118,z6]),(0,[z0,z1119,z2,z3,z4,z6]),(0,[z0,z201,z2,z20,z3,z6]),(0,[z0,z326,z30,z3,z4,z6]),(0,[z0,z1,z2,z258,z56,z6]),(0,[z0,z1,z2,z20,z3,z417])],[(0,[z31,z0,z1,z2,z572,z6]),(0,[z59,z2,z561,z3,z4,z6]),(1,[z0,z1,z3,z4,z902]),(0,[z0,z385,z1,z2,z113,z6])],[(0,[z0,z1,z2,z1120,z4,z6]),(0,[z23,z598,z1,z3,z4,z6]),(0,[z31,z0,z201,z2,z4,z6]),(1,[z0,z2,z3,z4,z771]),(0,[z0,z157,z1,z104,z4,z6]),(0,[z0,z164,z2,z3,z4,z417])],[(0,[z31,z0,z1,z2,z566,z6]),(0,[z0,z2,z3,z4,z1121,z6]),(0,[z31,z0,z1,z2,z270,z6]),(0,[z31,z0,z1,z2,z83,z6]),(0,[z0,z1122,z1,z2,z3,z6])],[(0,[z31,z0,z201,z2,z8,z6]),(0,[z36,z191,z1,z2,z3,z4]),(0,[z31,z0,z1,z2,z632,z6]),(0,[z1123,z1,z2,z3,z4,z6]),(0,[z0,z1,z1124,z3,z4,z6]),(0,[z31,z0,z1,z89,z3,z91]),(0,[z0,z2,z3,z6,z278,z281])]],
   [[(0,[z0,z157,z1,z40,z4,z6]),(0,[z0,z2,z790,z129,z4,z6]),(0,[z31,z0,z1,z747,z2,z6]),(0,[z31,z0,z1,z2,z3,z751]),(0,[z0,z559,z1,z2,z3,z179]),(0,[z0,z1,z2,z20,z6,z282])],[(0,[z0,z1125,z1,z3,z4,z6]),(0,[z31,z0,z1,z2,z382,z6]),(0,[z0,z1,z2,z20,z3,z436]),(0,[z31,z0,z1,z2,z10,z6])],[(0,[z0,z301,z2,z3,z53,z6]),(0,[z0,z157,z1,z132,z104,z6]),(0,[z0,z1126,z2,z3,z4,z6]),(0,[z0,z1,z367,z3,z4,z91]),(0,[z31,z841,z1,z2,z3,z6])],[(0,[z0,z1,z241,z27,z3,z4]),(0,[z31,z0,z1,z2,z578,z6]),(0,[z1127,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1128]),(0,[z0,z1129,z1,z2,z4,z6]),(0,[z7,z1,z2,z8,z4,z6]),(0,[z0,z183,z67,z2,z97,z6]),(0,[z0,z1,z55,z32,z99,z6]),(0,[z31,z0,z1,z2,z519,z6]),(0,[z0,z1,z2,z3,z11,z6])],[(0,[z0,z1,z1130,z3,z4,z6]),(0,[z0,z1,z2,z1131,z4,z6]),(0,[z31,z1127,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1132]),(0,[z0,z757,z1,z2,z3,z4]),(0,[z0,z1,z920,z3,z4,z6]),(0,[z0,z1,z2,z6,z282,z462])],[(0,[z0,z144,z2,z3,z76,z6]),(0,[z0,z1,z2,z241,z20,z3]),(0,[z0,z1133,z2,z3,z4,z6]),(0,[z0,z183,z1,z2,z4,z6]),(0,[z0,z39,z2,z78,z395,z6]),(0,[z0,z1,z2,z3,z734,z6])],[(0,[z0,z1,z2,z20,z3,z293]),(0,[z0,z1,z2,z20,z216,z6]),(0,[z31,z1,z2,z3,z6,z90]),(0,[z0,z2,z784,z3,z4,z6])]],
   [[(0,[z31,z0,z684,z1,z2,z6]),(0,[z0,z1,z2,z1134,z4,z6]),(0,[z0,z1,z2,z3,z1135,z6]),(0,[z0,z1,z2,z732,z4,z6]),(0,[z0,z1,z2,z181,z9,z6]),(0,[z31,z0,z39,z1,z2,z6]),(0,[z31,z0,z1,z2,z587,z6]),(0,[z0,z1,z2,z3,z1136,z6]),(0,[z0,z111,z1,z266,z3,z6]),(0,[z31,z0,z1,z2,z6,z462])],[(0,[z0,z1,z2,z1137,z4,z6]),(0,[z0,z1,z1138,z3,z4,z6]),(0,[z0,z1,z2,z3,z76,z167]),(0,[z0,z2,z1139,z3,z4,z6]),(0,[z31,z0,z812,z1,z2,z6]),(0,[z0,z1,z2,z3,z1140,z4]),(0,[z0,z85,z1,z2,z3,z554])],[(0,[z31,z0,z1,z2,z3,z6]),(0,[z0,z1141,z1,z3,z4,z6]),(0,[z43,z1,z2,z3,z743,z6]),(0,[z0,z14,z480,z3,z4,z6]),(0,[z0,z1142,z2,z3,z4,z6]),(0,[z31,z0,z164,z2,z3,z6]),(0,[z0,z1,z2,z20,z896,z6])],[(0,[z0,z1,z32,z40,z4,z6]),(0,[z0,z2,z339,z3,z4,z6]),(0,[z0,z1,z2,z3,z1143,z6]),(0,[z0,z1,z2,z482,z20,z3]),(0,[z31,z0,z1,z2,z70,z6]),(0,[z1144,z1,z2,z3,z4,z6]),(0,[z0,z52,z2,z3,z53,z6]),(0,[z0,z1,z2,z3,z1145,z6]),(0,[z0,z1,z131,z3,z199,z6]),(0,[z0,z1,z2,z3,z119,z176])],[(0,[z0,z1146,z1,z2,z4,z6]),(0,[z0,z103,z261,z1,z2,z6])],[(0,[z0,z1,z2,z3,z1147,z6]),(0,[z0,z102,z1,z104,z4,z6]),(0,[z0,z102,z1,z20,z3,z6]),(0,[z371,z1,z2,z3,z42,z6]),(0,[z1148,z1,z2,z3,z4,z6])],[(0,[z195,z1,z861,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1149]),(0,[z0,z2,z3,z4,z6,z1150]),(0,[z0,z1,z2,z1151,z3,z4]),(0,[z0,z133,z2,z20,z3,z6]),(0,[z0,z92,z2,z3,z119,z4])],[(0,[z0,z1,z2,z3,z1152,z6])]],
   [[(0,[z0,z102,z1,z40,z4,z6]),(0,[z31,z195,z1,z162,z3,z6]),(0,[z0,z1,z2,z3,z743,z6]),(0,[z0,z67,z2,z216,z97,z6]),(0,[z0,z157,z1,z266,z4,z6]),(0,[z0,z1,z381,z3,z199,z6]),(0,[z31,z0,z1,z2,z608,z6])],[(0,[z0,z1,z2,z3,z4,z1153]),(0,[z0,z1,z2,z1154,z4,z6]),(0,[z0,z1022,z2,z3,z4,z6])],[(0,[z1155,z0,z1,z2,z3,z6]),(0,[z7,z1,z27,z8,z4,z6]),(0,[z0,z269,z1,z2,z20,z3]),(1,[z0,z2,z3,z853,z6])],[(0,[z0,z242,z30,z3,z4,z6]),(0,[z0,z1,z1156,z3,z4,z6]),(0,[z1,z2,z1157,z3,z4,z6])],[(0,[z1065,z0,z1,z2,z3,z6]),(0,[z121,z1,z2,z109,z4,z6]),(0,[z0,z1158,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z268,z6]),(0,[z0,z103,z2,z632,z4,z6]),(0,[z0,z1,z2,z3,z4,z1159]),(0,[z194,z58,z1,z2,z3,z4]),(0,[z0,z1160,z1,z2,z3,z6])],[(0,[z1161,z1,z2,z3,z4,z6]),(0,[z31,z0,z122,z58,z1,z2]),(0,[z31,z1144,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z76,z49]),(0,[z31,z0,z103,z1,z2,z6]),(0,[z31,z0,z2,z339,z3,z6]),(0,[z0,z1,z2,z4,z1162,z6])],[(0,[z43,z1,z2,z3,z44,z6]),(0,[z0,z1,z871,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1163]),(0,[z31,z994,z1,z2,z3,z6])]],
   [[(0,[z348,z1,z2,z109,z4,z6]),(0,[z1164,z1,z2,z3,z4,z6]),(0,[z0,z1,z341,z2,z3,z4]),(0,[z0,z1,z768,z104,z4,z6]),(0,[z0,z85,z92,z2,z3,z118])],[(0,[z0,z1,z2,z3,z4,z1165]),(0,[z31,z0,z191,z1,z2,z6])],[(0,[z0,z1,z2,z3,z1166,z6]),(0,[z0,z103,z341,z2,z3,z4]),(0,[z31,z0,z157,z1,z55,z6]),(0,[z0,z235,z2,z20,z3,z6]),(0,[z0,z459,z111,z1,z112,z6]),(0,[z31,z840,z1,z2,z3,z6])],[(0,[z1091,z0,z1,z2,z289,z6]),(0,[z0,z1,z2,z3,z4,z1167]),(0,[z0,z1,z2,z3,z1168,z6]),(0,[z31,z36,z0,z58,z1,z2]),(0,[z31,z297,z1,z2,z3,z6]),(0,[z31,z0,z356,z1,z2,z6]),(0,[z0,z1169,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1170]),(0,[z0,z1,z2,z20,z3,z379]),(1,[z0,z1,z2,z3,z735])],[(0,[z0,z1,z2,z3,z1171,z6]),(0,[z171,z0,z1,z2,z3,z6]),(0,[z35,z1,z2,z3,z4,z867])],[(0,[z0,z269,z1,z2,z3,z181]),(0,[z0,z1,z2,z1172,z4,z6]),(0,[z0,z1,z2,z3,z6,z1173]),(0,[z818,z1,z2,z3,z4,z6]),(0,[z0,z1,z55,z32,z4,z436]),(0,[z0,z164,z2,z3,z4,z379]),(0,[z31,z190,z1,z2,z113,z6]),(0,[z31,z0,z1080,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1174,z6]),(0,[z31,z0,z144,z2,z3,z6]),(0,[z0,z1,z2,z3,z1175,z6]),(0,[z0,z202,z2,z30,z3,z4]),(0,[z31,z190,z103,z1,z2,z6])],[(0,[z31,z0,z102,z1,z4,z6]),(0,[z0,z1,z2,z3,z4,z1176]),(0,[z0,z1,z2,z3,z4,z1177]),(0,[z0,z157,z221,z1,z2,z6])]]]

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
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 512).take 519) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1031).take 215) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1246)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [512, 519, 215] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 91).take 84).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 175).take 81).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [91, 84, 81] = true :=
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

end PEqualNP.Outside.L_meta_38443

theorem PEqualNP.Outside.L_meta_38443 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372928 * 2 ^ 32 + 3938511360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372928 * 2 ^ 32 + 3938511360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38443.solve
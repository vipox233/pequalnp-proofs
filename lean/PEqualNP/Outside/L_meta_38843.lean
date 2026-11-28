import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38843

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
  Nat.testBit (4276808928 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0021b3c4461c6314#64 ++ 0x40021b3c4461c631#64 ++ 0x3067f7c4c63ce73f#64 ++ 0xa3067f7c4c63ce73#64 : BitVec 256),
   (0x008b80dd06c52948#64 ++ 0x8008b80dd06c5294#64 ++ 0xd19b89ff07c739cf#64 ++ 0x7d19b89ff07c739c#64 : BitVec 256),
   (0x26140c02980294a1#64 ++ 0x026140c02980294a#64 ++ 0xee1c0e07f807fffe#64 ++ 0xeee1c0e07f807fff#64 : BitVec 256),
   (0x1b600f682b683e0e#64 ++ 0x01b600f682b683e0#64 ++ 0xffe00ff83ff83e0d#64 ++ 0xfffe00ff83ff83e0#64 : BitVec 256),
   (0x4dded00035b7c000#64 ++ 0x04dded00035b7c00#64 ++ 0x7ffff0003fffc00b#64 ++ 0xf7ffff0003fffc00#64 : BitVec 256),
   (0x8fff6fb7c0000000#64 ++ 0x08fff6fb7c000000#64 ++ 0x8fffffffc0000007#64 ++ 0xf8fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [7, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3067f7c4c63ce73f 0xa3067f7c4c63ce73

def z1 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19b89ff07c739cf 0x7d19b89ff07c739c

def z2 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe00ff83ff83e0d 0xfffe00ff83ff83e0

def z3 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xee1c0e07f807fffe 0xeee1c0e07f807fff

def z4 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffff0003fffc00b 0xf7ffff0003fffc00

def z5 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z6 : W := mkw 0xcffffff7f7bfe314 0x4cffffff7f7bfe31 0xffffffffffffe73f 0xfffffffffffffe73

def z7 : W := mkw 0x1b61bfe46f3c7716 0x41b61bfe46f3c771 0x3e67f7c4fe3ce73f 0xa3e67f7c4fe3ce73

def z8 : W := mkw 0x0b600f2000000000 0x00b600f200000000 0x0e60060000000000 0x80e6006000000000

def z9 : W := mkw 0x6fdfdcdfbff7fde9 0x86fdfdcdfbff7fde 0xffffffffffffffff 0xffffffffffffffff

def z10 : W := mkw 0x0020b300441c4214 0x40020b300441c421 0x3067f600c63cc63b 0xa3067f600c63cc63

def z11 : W := mkw 0x0dde400021200000 0x00dde40002120000 0x7ffff0003ff8000b 0xf7ffff0003ff8000

def z12 : W := mkw 0x22000c02880014a1 0x022000c02880014a 0xa0040e07c004fffe 0xaa0040e07c004fff

def z13 : W := mkw 0x0000004802402808 0x0000000480240280 0xd18009f807c0380d 0x7d18009f807c0380

def z14 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0x2e040600f800c630 0x82e040600f800c63

def z15 : W := mkw 0x02000c0008001400 0x002000c000800140 0xee000e0038003e0c 0xeee000e0038003e0

def z16 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x01e3f1f800000001 0x101e3f1f80000000

def z17 : W := mkw 0x008b00dd02402948 0x8008b00dd0240294 0x819b89ff000039c7 0x7819b89ff000039c

def z18 : W := mkw 0x0020330040184214 0x4002033004018421 0x20647600c038c630 0x820647600c038c63

def z19 : W := mkw 0x000180cc06c52948 0x8000180cc06c5294 0x500381c407c739cf 0x2500381c407c739c

def z20 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000000739c8 0x040000000000739c

def z21 : W := mkw 0x269f0c97980294a1 0x0269f0c97980294a 0xef9f8ffff807ffff 0xfef9f8ffff807fff

def z22 : W := mkw 0x0ffe4f2000000000 0x00ffe4f200000000 0x8ffffff800000007 0xf8ffffff80000000

def z23 : W := mkw 0x4000900035b7c000 0x04000900035b7c00 0x700000003fffc008 0x0700000003fffc00

def z24 : W := mkw 0x0021238440000000 0x0002123844000000 0x0067f7c4c0000007 0xa0067f7c4c000000

def z25 : W := mkw 0x100000482b683e0e 0x0100000482b683e0 0x700000003ff83e08 0x0700000003ff83e0

def z26 : W := mkw 0x008a804806c52808 0x0008a804806c5280 0xd19b89f807c7380f 0x7d19b89f807c7380

def z27 : W := mkw 0x0414000010028000 0x0041400001002800 0x6e1c00003807c00a 0xe6e1c00003807c00

def z28 : W := mkw 0x4dfef30075bfc214 0x44dfef30075bfc21 0x7ffff600ffffc63b 0xf7ffff600ffffc63

def z29 : W := mkw 0x0940000021200000 0x0094000002120000 0x7fe000003ff80009 0xf7fe000003ff8000

def z30 : W := mkw 0x1960036823682a0e 0x01960036823682a0 0x11e001f807f80001 0x111e001f807f8000

def z31 : W := mkw 0xaf746f22d80294a1 0x0af746f22d80294a 0x2e647600f800c630 0x82e647600f800c63

def z32 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xeffffffff807ffff 0xfeffffffff807fff

def z33 : W := mkw 0xcf747f22f132c000 0x0cf747f22f132c00 0x2e647600f838c000 0x82e647600f838c00

def z34 : W := mkw 0x008b80d506042100 0x0008b80d50604210 0x919b89ff0604210f 0x7919b89ff0604210

def z35 : W := mkw 0x3f740f22b92a96a7 0x03f740f22b92a96a 0xee7c0e07f83ffffe 0xeee7c0e07f83ffff

def z36 : W := mkw 0x0000800004850000 0x0000080000485000 0x5000000007c70008 0x05000000007c7000

def z37 : W := mkw 0x2f540c02b92294a1 0x02f540c02b92294a 0xfffc0e07ffffffff 0xffffc0e07fffffff

def z38 : W := mkw 0x849f6097c0000000 0x0849f6097c000000 0x001ff007c0000002 0x0001ff007c000000

def z39 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xee040e00f800fe3c 0xeee040e00f800fe3

def z40 : W := mkw 0x26148c4a9ec7bde9 0x826148c4a9ec7bde 0xfe1c0e07ffc7fffe 0xefe1c0e07ffc7fff

def z41 : W := mkw 0x5ffedf683ffffe0e 0x05ffedf683ffffe0 0xfffffff83ffffe0f 0xffffffff83ffffe0

def z42 : W := mkw 0x9beb6ffd6b683e0e 0x09beb6ffd6b683e0 0xffe3fff83ff83e0d 0xfffe3fff83ff83e0

def z43 : W := mkw 0x008a000000810000 0x0008a00000081000 0x4198000001c30000 0x54198000001c3000

def z44 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z45 : W := mkw 0x00abb3dd46dd6b5c 0xc00abb3dd46dd6b5 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0180803000318c0 0x4c0180803000318c

def z47 : W := mkw 0x0dde400000000000 0x00dde40000000000 0x0f98000000000000 0x50f9800000000000

def z48 : W := mkw 0x2635bfc6de1ef7b5 0x42635bfc6de1ef7b 0x3e67f7c4fe3ce73f 0xa3e67f7c4fe3ce73

def z49 : W := mkw 0x808b609540000000 0x0808b60954000000 0x0003f00000000000 0x00003f0000000000

def z50 : W := mkw 0x1b61bfec6f7c7f1e 0x41b61bfec6f7c7f1 0xffe3fff83ff83e0d 0xfffe3fff83ff83e0

def z51 : W := mkw 0x008b90dd06dd6b5c 0xc008b90dd06dd6b5 0xf19b89ff07ffffff 0x7f19b89ff07fffff

def z52 : W := mkw 0x4d5450003132c000 0x04d5450003132c00 0x6e7c7000383fc00a 0xe6e7c7000383fc00

def z53 : W := mkw 0x008a800004850000 0x0008a80000485000 0x519b800007c7000b 0x7519b800007c7000

def z54 : W := mkw 0x0d54400000000000 0x00d5440000000000 0x0e64700000000000 0x80e6470000000000

def z55 : W := mkw 0x20000000180294a1 0x020000000180294a 0x600000003807fff8 0x0600000003807fff

def z56 : W := mkw 0x24140002900280a1 0x024140002900280a 0x201c0607c007e7fe 0xa201c0607c007e7f

def z57 : W := mkw 0x5fffdffd3fffff4e 0x85fffdffd3fffff4 0xffffffff3fffffcf 0xfffffffff3fffffc

def z58 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0180807000739ce 0x6c0180807000739c

def z59 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0x3fe007f83ff80601 0x93fe007f83ff8060

def z60 : W := mkw 0xcffffffff7f7e948 0x8cffffffff7f7e94 0xfffffffffffff9cf 0xffffffffffffff9c

def z61 : W := mkw 0x82212fffc2402948 0x882212fffc240294 0x80000fffc00039c4 0x080000fffc00039c

def z62 : W := mkw 0x12200f680a483e0e 0x012200f680a483e0 0x80000ff800003e04 0x080000ff800003e0

def z63 : W := mkw 0x49cad00025b54000 0x049cad00025b5400 0x11e3f00007f80001 0x111e3f00007f8000

def z64 : W := mkw 0x2635bfc6de1ef7b5 0x42635bfc6de1ef7b 0xfe7fffc7fe3fffff 0xefe7fffc7fe3ffff

def z65 : W := mkw 0x008a001900c10848 0x8008a001900c1084 0xc198083b01c318c0 0x5c198083b01c318c

def z66 : W := mkw 0x8f746f22c0000000 0x08f746f22c000000 0x0e647600c0000000 0x80e647600c000000

def z67 : W := mkw 0x02000c0000000000 0x002000c000000000 0x8e000e0000000004 0xe8e000e000000000

def z68 : W := mkw 0x2435b3c6d61ee3b5 0x42435b3c6d61ee3b 0x307ff7c7c63fe7ff 0xa307ff7c7c63fe7f

def z69 : W := mkw 0x5fde4c2839e39c0a 0x05fde4c2839e39c0 0xcf98083839c31800 0x5cf98083839c3180

def z70 : W := mkw 0x8fde4c3380000000 0x08fde4c338000000 0x8f9c0e3fc0000006 0xf8f9c0e3fc000000

def z71 : W := mkw 0x002123c442082204 0x0002123c44208220 0x3067f7c4c638260f 0xa3067f7c4c638260

def z72 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0x118381f807c00001 0x1118381f807c0000

def z73 : W := mkw 0x1b600f2029281606 0x01b600f202928160 0x2e60060038380600 0x82e6006003838060

def z74 : W := mkw 0x49cad00025b54000 0x049cad00025b5400 0x31e7f00007fcc00b 0xb31e7f00007fcc00

def z75 : W := mkw 0x4ddfd0dd37f7e948 0x84ddfd0dd37f7e94 0x7ffff1f83fffc00b 0xf7ffff1f83fffc00

def z76 : W := mkw 0x4dde401931e38848 0x84dde401931e3884 0xcf98083b39c318c0 0x5cf98083b39c318c

def z77 : W := mkw 0x008b009500000000 0x0008b00950000000 0x819b89ff00000007 0x7819b89ff0000000

def z78 : W := mkw 0x9fff6fffeb683e0e 0x09fff6fffeb683e0 0xfffffffffff83e0f 0xffffffffffff83e0

def z79 : W := mkw 0x849fe0dfc6c52948 0x8849fe0dfc6c5294 0xd19ff9ffc7c739cf 0x7d19ff9ffc7c739c

def z80 : W := mkw 0x0000900004144000 0x0000090000414400 0x3067f604c63ce73f 0xa3067f604c63ce73

def z81 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x1063f1c4063c210f 0x21063f1c4063c210

def z82 : W := mkw 0x9fde4c3ba9601c0a 0x09fde4c3ba9601c0 0xcf98083b39c01800 0x5cf98083b39c0180

def z83 : W := mkw 0xcfffffb7f5b7c000 0x0cfffffb7f5b7c00 0xffffffffffffc00f 0xfffffffffffffc00

def z84 : W := mkw 0x82212fb7c0000000 0x082212fb7c000000 0x80000fffc0000004 0x080000fffc000000

def z85 : W := mkw 0x4ddff08475b7c110 0x44ddff08475b7c11 0x7ffff004ffffc13b 0xf7ffff004ffffc13

def z86 : W := mkw 0x0000000000000000 0x0000000000000000 0x20040604c004e73e 0xa20040604c004e73

def z87 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffff604ffffe73f 0xf7ffff604ffffe73

def z88 : W := mkw 0x0000000000000000 0x0000000000000000 0x818009f800000005 0x7818009f80000000

def z89 : W := mkw 0x09ca800025a50000 0x009ca800025a5000 0x7ffb80003fff000b 0xf7ffb80003fff000

def z90 : W := mkw 0x06140c0280000000 0x006140c028000000 0x8e1c0e07c0000006 0xe8e1c0e07c000000

def z91 : W := mkw 0x00009040061c6314 0x400009040061c631 0x30040604c63ce73e 0xa30040604c63ce73

def z92 : W := mkw 0x26149c429e1ef7b5 0x426149c429e1ef7b 0xfe1c0e07fe3ffffe 0xefe1c0e07fe3ffff

def z93 : W := mkw 0x36140c4abb6abeaf 0x036140c4abb6abea 0xfe1c0e07fffffffe 0xefe1c0e07fffffff

def z94 : W := mkw 0x8ffe4f3380000000 0x08ffe4f338000000 0x8ff80ffb00000005 0xf8ff80ffb0000000

def z95 : W := mkw 0x1beb8ffd2fed3f4e 0x81beb8ffd2fed3f4 0xfffb8fff3fff3fcf 0xffffb8fff3fff3fc

def z96 : W := mkw 0x3b600f6aab683eaf 0x03b600f6aab683ea 0xffe00ffffff83ffd 0xfffe00ffffff83ff

def z97 : W := mkw 0x8f756fa6c0000000 0x08f756fa6c000000 0x0e67f7c4c0000007 0xa0e67f7c4c000000

def z98 : W := mkw 0x0000804806c52948 0x80000804806c5294 0xd018080707c739ce 0x6d018080707c739c

def z99 : W := mkw 0x4dde400031a38000 0x04dde400031a3800 0x4f98000039c30000 0x54f98000039c3000

def z100 : W := mkw 0x000180dd06442948 0x8000180dd0644294 0x900389ff060439cf 0x2900389ff060439c

def z101 : W := mkw 0x8ddf6097c0000000 0x08ddf6097c000000 0x0ffff007c0000003 0xf0ffff007c000000

def z102 : W := mkw 0xcfffffb7d497c000 0x0cfffffb7d497c00 0x8fffffffc007c007 0xf8fffffffc007c00

def z103 : W := mkw 0x000180dd06c52948 0x8000180dd06c5294 0xd00009ff07c739cc 0x0d00009ff07c739c

def z104 : W := mkw 0x0b600f2021200000 0x00b600f202120000 0xffe00ff83ff8000d 0xfffe00ff83ff8000

def z105 : W := mkw 0x0000004002082204 0x0000000400208220 0x3000000006382608 0x0300000000638260

def z106 : W := mkw 0x12212fec4a483f1e 0x412212fec4a483f1 0x80000ffcc0003f34 0x080000ffcc0003f3

def z107 : W := mkw 0x0000804806c52948 0x80000804806c5294 0x5000000007c739c8 0x05000000007c739c

def z108 : W := mkw 0x00009040061c6314 0x400009040061c631 0x30000000063ce738 0x030000000063ce73

def z109 : W := mkw 0x008b809504850140 0x8008b80950485014 0x001b8007000701c2 0x0001b8007000701c

def z110 : W := mkw 0x008b809504850140 0x8008b80950485014 0xc01b8807000739ce 0x6c01b8807000739c

def z111 : W := mkw 0x92212fffca483e0e 0x092212fffca483e0 0x80000fffc0003e04 0x080000fffc0003e0

def z112 : W := mkw 0x89ca403100000000 0x089ca40310000000 0x0180003800000000 0x1018000380000000

def z113 : W := mkw 0x24140002900280a1 0x024140002900280a 0x001c0007c007c1f2 0x0001c0007c007c1f

def z114 : W := mkw 0x6dded002b5b7c0a1 0x06dded002b5b7c0a 0x7ffff007ffffc1fb 0xf7ffff007ffffc1f

def z115 : W := mkw 0x02000c0008001400 0x002000c000800140 0xee040e04f804ff3e 0xeee040e04f804ff3

def z116 : W := mkw 0x100090482f7c7f1e 0x4100090482f7c7f1 0x700000003ffcff38 0x0700000003ffcff3

def z117 : W := mkw 0x1b61bfec6f7c7f1e 0x41b61bfec6f7c7f1 0xffe7fffcfffcff3f 0xfffe7fffcfffcff3

def z118 : W := mkw 0x0001b08444144110 0x40001b0844414411 0x0003f00000000000 0x00003f0000000000

def z119 : W := mkw 0x8fde4c3380000000 0x08fde4c338000000 0x8f98083b00000000 0x58f98083b0000000

def z120 : W := mkw 0x0001008400000000 0x0000100840000000 0x000381c400000007 0x2000381c40000000

def z121 : W := mkw 0x1beb0ffd2b683e0e 0x01beb0ffd2b683e0 0xfffb8fff3ff83e0f 0xffffb8fff3ff83e0

def z122 : W := mkw 0x8dff63b7c0000000 0x08dff63b7c000000 0x01fff1ffc0000003 0x101fff1ffc000000

def z123 : W := mkw 0x4ddfd0dd37f7e948 0x84ddfd0dd37f7e94 0xfffff9ff3ffff9cf 0xffffff9ff3ffff9c

def z124 : W := mkw 0x4000904837f7e948 0x84000904837f7e94 0x700000003ffff9c8 0x0700000003ffff9c

def z125 : W := mkw 0x000100dd02402948 0x8000100dd0240294 0x800009ff000039c4 0x0800009ff000039c

def z126 : W := mkw 0x0000900004144000 0x0000090000414400 0x3067f000063cc00b 0xa3067f000063cc00

def z127 : W := mkw 0x0000000000000000 0x0000000000000000 0x0067f00000000003 0xa0067f0000000000

def z128 : W := mkw 0x4d5450003132c000 0x04d5450003132c00 0x2e6470003838c000 0x82e6470003838c00

def z129 : W := mkw 0x8fff6fb7e1200000 0x08fff6fb7e120000 0xfffffffffff8000f 0xffffffffffff8000

def z130 : W := mkw 0x59ead36827fd6a0e 0x059ead36827fd6a0 0x11e3f1f807f80001 0x111e3f1f807f8000

def z131 : W := mkw 0x400090001497c000 0x0400090001497c00 0x000000000007c000 0x0000000000007c00

def z132 : W := mkw 0x6fde4c02b9a394a1 0x06fde4c02b9a394a 0xcf98080339c318c0 0x5cf98080339c318c

def z133 : W := mkw 0x0000804806c52948 0x80000804806c5294 0x1000000007c00000 0x01000000007c0000

def z134 : W := mkw 0x4000904037bfe314 0x44000904037bfe31 0x700000003fffe738 0x0700000003fffe73

def z135 : W := mkw 0x002123c442082314 0x4002123c44208231 0x000007c4c0002734 0x0000007c4c000273

def z136 : W := mkw 0x9fff6fb7e9281606 0x09fff6fb7e928160 0xaffffffff8380607 0xfaffffffff838060

def z137 : W := mkw 0x09ca400000000000 0x009ca40000000000 0x01e3f00000000001 0x101e3f0000000000

def z138 : W := mkw 0x196003682b683e0e 0x0196003682b683e0 0x71e001f83ff83e09 0x171e001f83ff83e0

def z139 : W := mkw 0x0020034002082204 0x0002003400208220 0x106001c006380001 0x0106001c00638000

def z140 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xfff80fff3fff3fcf 0xffff80fff3fff3fc

def z141 : W := mkw 0x4dfff3c477bfe314 0x44dfff3c477bfe31 0x7ffff7c4ffffe73f 0xf7ffff7c4ffffe73

def z142 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0x2e1c0607f807c7f2 0x82e1c0607f807c7f

def z143 : W := mkw 0x0000800004850140 0x8000080000485014 0x00000000000701c0 0x000000000000701c

def z144 : W := mkw 0xdffffffffffffe0e 0x0dffffffffffffe0 0xfffffffffffffe0f 0xffffffffffffffe0

def z145 : W := mkw 0x22000c00180294a1 0x022000c00180294a 0xee000e003807fffc 0xeee000e003807fff

def z146 : W := mkw 0x1b600f6823682a0e 0x01b600f6823682a0 0x9fe00ff807f80005 0xf9fe00ff807f8000

def z147 : W := mkw 0x1b400c2829601c0a 0x01b400c2829601c0 0xcf80083839c01800 0x5cf80083839c0180

def z148 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xce180803380318c0 0x4ce180803380318c

def z149 : W := mkw 0x0020330040184214 0x4002033004018421 0x20647604c03ce73e 0xa20647604c03ce73

def z150 : W := mkw 0x449ed0001497c000 0x0449ed0001497c00 0x001ff0000007c002 0x0001ff0000007c00

def z151 : W := mkw 0x208b80dd1ec7bde9 0x8208b80dd1ec7bde 0xf19b89ff3fc7ffff 0x7f19b89ff3fc7fff

def z152 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0xf07fffc7c63fffff 0xef07fffc7c63ffff

def z153 : W := mkw 0x8b612fb7c0000000 0x08b612fb7c000000 0x8fe00fffc0000005 0xf8fe00fffc000000

def z154 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x81fbf9ff00000007 0x781fbf9ff0000000

def z155 : W := mkw 0x008b809504850140 0x8008b80950485014 0x819b89ff000701c7 0x7819b89ff000701c

def z156 : W := mkw 0x6fde4c02b9a394a1 0x06fde4c02b9a394a 0xef9c0e07f9c7fffe 0xfef9c0e07f9c7fff

def z157 : W := mkw 0x00abb3d5461c6314 0x400abb3d5461c631 0xb1ffffffc63ce73f 0xfb1ffffffc63ce73

def z158 : W := mkw 0x0000000000000000 0x0000000000000000 0x200006000000260c 0xa200006000000260

def z159 : W := mkw 0x8fffefb7c4850000 0x08fffefb7c485000 0xdfffffffc7c7000f 0xfdfffffffc7c7000

def z160 : W := mkw 0x228b8cdf8ec53de9 0x8228b8cdf8ec53de 0xd19b8fffc7c73fff 0x7d19b8fffc7c73ff

def z161 : W := mkw 0xafde4c33980294a1 0x0afde4c33980294a 0xcf98083b380318c0 0x5cf98083b380318c

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000040004210e 0x2000000040004210

def z163 : W := mkw 0x1000000029281606 0x0100000002928160 0x2000000038380600 0x0200000003838060

def z164 : W := mkw 0x8960632040000000 0x0896063204000000 0x0060700000000000 0x0006070000000000

def z165 : W := mkw 0x0021b3dd465c6b5c 0xc0021b3dd465c6b5 0xb067ffffc63cffff 0xab067ffffc63cfff

def z166 : W := mkw 0x0b600f2000000000 0x00b600f200000000 0x8fe00ff800000005 0xf8fe00ff80000000

def z167 : W := mkw 0x24140002900280a1 0x024140002900280a 0x00040000c000c030 0x000040000c000c03

def z168 : W := mkw 0x49cbd0dd27f56948 0x849cbd0dd27f5694 0xd1fbf9ff07ff39cf 0x7d1fbf9ff07ff39c

def z169 : W := mkw 0x8fffefffc6c52948 0x88fffefffc6c5294 0xdfffffffc7c739cf 0xfdfffffffc7c739c

def z170 : W := mkw 0x008b009500000000 0x0008b00950000000 0xc19b89ff000739cf 0x7c19b89ff000739c

def z171 : W := mkw 0x0dde400000000000 0x00dde40000000000 0x0ffff00000000003 0xf0ffff0000000000

def z172 : W := mkw 0x8fff6ff7c2082314 0x48fff6ff7c208231 0x8fffffffc0002737 0xf8fffffffc000273

def z173 : W := mkw 0x100000482b683e0e 0x0100000482b683e0 0xf18009f83ff83e0d 0x7f18009f83ff83e0

def z174 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3067f1c0063cc00b 0xa3067f1c0063cc00

def z175 : W := mkw 0x3f740f22b92a96a7 0x03f740f22b92a96a 0x2e640600f838c630 0x82e640600f838c63

def z176 : W := mkw 0x3f740f6abb6abeaf 0x03f740f6abb6abea 0xfffc0fffffffffff 0xffffc0ffffffffff

def z177 : W := mkw 0x02000c0280000000 0x002000c028000000 0x80000e07c0000004 0x080000e07c000000

def z178 : W := mkw 0x82abafffc6c52948 0x882abafffc6c5294 0xd19b8fffc7c739cf 0x7d19b8fffc7c739c

def z179 : W := mkw 0x3f540c2ab9629cab 0x03f540c2ab9629ca 0xef9c0e3ff9c7fffe 0xfef9c0e3ff9c7fff

def z180 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xdfe009f83ff81801 0x5dfe009f83ff8180

def z181 : W := mkw 0x1b612fec6b683e0e 0x01b612fec6b683e0 0xffe7fffcfff83e0f 0xfffe7fffcfff83e0

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018080700000006 0x6801808070000000

def z183 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x5ffbf0003ffb0001 0x55ffbf0003ffb000

def z184 : W := mkw 0x008b80c406852100 0x0008b80c40685210 0x519b81c407c7210f 0x7519b81c407c7210

def z185 : W := mkw 0xcfff6fb7f1a38000 0x0cfff6fb7f1a3800 0xcffffffff9c30007 0xfcffffffff9c3000

def z186 : W := mkw 0x4dde400031a38000 0x04dde400031a3800 0x4ffff00039c30003 0xf4ffff00039c3000

def z187 : W := mkw 0x4dded04837f7e808 0x04dded04837f7e80 0xfffff9f83ffff80f 0xffffff9f83ffff80

def z188 : W := mkw 0x8fff6fb7d0028000 0x08fff6fb7d002800 0xeffffffff807c00f 0xfeffffffff807c00

def z189 : W := mkw 0xa49f6097d00280a1 0x0a49f6097d00280a 0x001ff007c007c1f2 0x0001ff007c007c1f

def z190 : W := mkw 0x0001b08444144110 0x40001b0844414411 0x0007f004c004c132 0x00007f004c004c13

def z191 : W := mkw 0x849ff097c4144110 0x4849ff097c414411 0x001ff007c004c132 0x0001ff007c004c13

def z192 : W := mkw 0x102003482b683e0e 0x0102003482b683e0 0x706007c03ff83e0d 0xa706007c03ff83e0

def z193 : W := mkw 0xafde4c33980294a1 0x0afde4c33980294a 0xef9c0e3ff807fffe 0xfef9c0e3ff807fff

def z194 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x11fff00007ffc003 0x111fff00007ffc00

def z195 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0x919b89ff07c00007 0x7919b89ff07c0000

def z196 : W := mkw 0x008a001900c10848 0x8008a001900c1084 0x0180003801c00000 0x10180003801c0000

def z197 : W := mkw 0x1bcb8cfd2fe53d4a 0x81bcb8cfd2fe53d4 0xdf9b89ff3fc739cf 0x7df9b89ff3fc739c

def z198 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x01e7f7fcc0000007 0xb01e7f7fcc000000

def z199 : W := mkw 0x0000004802402948 0x8000000480240294 0x00000000000039c0 0x000000000000039c

def z200 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x0fe7f7f8c0000001 0x90fe7f7f8c000000

def z201 : W := mkw 0x4dde50003132c000 0x04dde50003132c00 0x2ffff0003838c003 0xf2ffff0003838c00

def z202 : W := mkw 0x9f746f6aeb683e0e 0x09f746f6aeb683e0 0xffe47ff8fff83e0d 0xfffe47ff8fff83e0

def z203 : W := mkw 0x0001b08444144110 0x40001b0844414411 0x3067f004c63cc13b 0xa3067f004c63cc13

def z204 : W := mkw 0x0b612fa440000000 0x00b612fa44000000 0x8fe7fffcc0000007 0xf8fe7fffcc000000

def z205 : W := mkw 0x4dded04037bfe314 0x44dded04037bfe31 0x7ffff0003fffe73b 0xf7ffff0003fffe73

def z206 : W := mkw 0x002123c442082314 0x4002123c44208231 0x0067f7c4c0002737 0xa0067f7c4c000273

def z207 : W := mkw 0x0221bfc44e1c7714 0x40221bfc44e1c771 0xfe67ffc4fe3cff3f 0xefe67ffc4fe3cff3

def z208 : W := mkw 0x8fff6fffc2402948 0x88fff6fffc240294 0x8fffffffc00039c7 0xf8fffffffc00039c

def z209 : W := mkw 0x500090483ffffe0e 0x0500090483ffffe0 0x700000003ffffe08 0x0700000003ffffe0

def z210 : W := mkw 0x8fde4c3380000000 0x08fde4c338000000 0x8ffff83b00000003 0xf8ffff83b0000000

def z211 : W := mkw 0x449ed0001497c000 0x0449ed0001497c00 0x519ff00007c7c00b 0x7519ff00007c7c00

def z212 : W := mkw 0x049e800014878000 0x0049e80001487800 0x7f9f80003fc7c00b 0xf7f9f80003fc7c00

def z213 : W := mkw 0x269e8c029c8794a1 0x0269e8c029c8794a 0xff9f8e07ffc7ffff 0xfff9f8e07ffc7fff

def z214 : W := mkw 0x32200f6a8a483eaf 0x032200f6a8a483ea 0x80000fffc0003ff4 0x080000fffc0003ff

def z215 : W := mkw 0x0960032000000000 0x0096003200000000 0x01e001f800000001 0x101e001f80000000

def z216 : W := mkw 0x6fdedc02bdb7d4a1 0x06fdedc02bdb7d4a 0xfffffe07ffffffff 0xffffffe07fffffff

def z217 : W := mkw 0x22000c02980294a1 0x022000c02980294a 0xe0000e07f807fffc 0x0e0000e07f807fff

def z218 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x1063f1c006380001 0x01063f1c00638000

def z219 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xaffffffff800c637 0xfaffffffff800c63

def z220 : W := mkw 0xa2212fb7c80014a1 0x0a2212fb7c80014a 0x80000fffc0003ff4 0x080000fffc0003ff

def z221 : W := mkw 0x3b600f683b6abeaf 0x03b600f683b6abea 0xffe00ff83ffffffd 0xfffe00ff83ffffff

def z222 : W := mkw 0x4d54d00035b7c000 0x04d54d00035b7c00 0x7e6470003fffc008 0x87e6470003fffc00

def z223 : W := mkw 0x26140c02880014a1 0x026140c02880014a 0x8e1c0e07c0003ff6 0xe8e1c0e07c0003ff

def z224 : W := mkw 0x000180c406042100 0x0000180c40604210 0x100381c40604210f 0x2100381c40604210

def z225 : W := mkw 0x200090401e1ef7b5 0x4200090401e1ef7b 0x700000003e3ffff8 0x0700000003e3ffff

def z226 : W := mkw 0x008b009d00c10848 0x8008b009d00c1084 0xc19b89ff01c318c7 0x7c19b89ff01c318c

def z227 : W := mkw 0x24140002900280a1 0x024140002900280a 0xc01c0807c007f9fe 0x6c01c0807c007f9f

def z228 : W := mkw 0x449ed0001497c000 0x0449ed0001497c00 0x6e1ff0003807c00a 0xe6e1ff0003807c00

def z229 : W := mkw 0x44bff3c4569fe314 0x444bff3c4569fe31 0x307ff7c4c63fe73f 0xa307ff7c4c63fe73

def z230 : W := mkw 0x0960034023282204 0x0096003402328220 0x7fe007c03ff8260d 0xf7fe007c03ff8260

def z231 : W := mkw 0x0000004002082314 0x4000000400208231 0x0000000000002730 0x0000000000000273

def z232 : W := mkw 0x269f8cdf9ec7bde9 0x8269f8cdf9ec7bde 0xff9f8fffffc7ffff 0xfff9f8fffffc7fff

def z233 : W := mkw 0x4d54400031228000 0x04d5440003122800 0x0e00000038000000 0x00e0000003800000

def z234 : W := mkw 0x89ebe3fd46c52948 0x889ebe3fd46c5294 0x11e3f1f807c00001 0x111e3f1f807c0000

def z235 : W := mkw 0x12200f682b683e0e 0x012200f682b683e0 0xf0000ff83ff83e0c 0x0f0000ff83ff83e0

def z236 : W := mkw 0x26158cc69e06b5a1 0x026158cc69e06b5a 0xfe1f8fc7fe07ffff 0xefe1f8fc7fe07fff

def z237 : W := mkw 0xbfff6ffffb6abeaf 0x0bfff6ffffb6abea 0xffffffffffffffff 0xffffffffffffffff

def z238 : W := mkw 0x0000000800c10848 0x80000000800c1084 0x4000000001c318c0 0x04000000001c318c

def z239 : W := mkw 0x0020034002082204 0x0002003400208220 0x306007c00638260d 0xa306007c00638260

def z240 : W := mkw 0x002183c4060c2304 0x0002183c4060c230 0x306387c4063c270f 0xa306387c4063c270

def z241 : W := mkw 0x4021b3c477bfe314 0x44021b3c477bfe31 0x7067f7c4ffffe73f 0xa7067f7c4ffffe73

def z242 : W := mkw 0x0000000000000000 0x0000000000000000 0x200400000004c00a 0xa200400000004c00

def z243 : W := mkw 0x82212ff7c2082314 0x482212ff7c208231 0x80000fffc0002734 0x080000fffc000273

def z244 : W := mkw 0x26140c4a9a42bca9 0x026140c4a9a42bca 0xff9c0fffffc7ffff 0xfff9c0fffffc7fff

def z245 : W := mkw 0x1221bfec4e5c7f1e 0x41221bfec4e5c7f1 0xb067fffcc63cff3f 0xab067fffcc63cff3

def z246 : W := mkw 0x36340f6a9a4abeaf 0x036340f6a9a4abea 0xee1c0ffff807fffe 0xeee1c0ffff807fff

def z247 : W := mkw 0x8fdf4cb780000000 0x08fdf4cb78000000 0x8f9b89ff00000007 0x78f9b89ff0000000

def z248 : W := mkw 0x84bf6397c0000000 0x084bf6397c000000 0x007ff7c7c0000007 0xa007ff7c7c000000

def z249 : W := mkw 0x0021238440000000 0x0002123844000000 0x0063f1c000000001 0x00063f1c00000000

def z250 : W := mkw 0x1b400c2829601c0a 0x01b400c2829601c0 0xffe008383ff81809 0xfffe008383ff8180

def z251 : W := mkw 0xcfdedc33b5b7c000 0x0cfdedc33b5b7c00 0xfffff83b3fffc00b 0xffffff83b3fffc00

def z252 : W := mkw 0x20000000180294a1 0x020000000180294a 0x40000000380318c0 0x040000000380318c

def z253 : W := mkw 0x0000000000000000 0x0000000000000000 0x00040004c004c132 0x000040004c004c13

def z254 : W := mkw 0x8beb6fb7c0000000 0x08beb6fb7c000000 0x81e3ffffc0000005 0x181e3ffffc000000

def z255 : W := mkw 0x19eb83fd27ed2b4e 0x819eb83fd27ed2b4 0xd1fb89ff07ff39cf 0x7d1fb89ff07ff39c

def z256 : W := mkw 0x869f6c97c0000000 0x0869f6c97c000000 0x8e1ffe07c0000006 0xe8e1ffe07c000000

def z257 : W := mkw 0xafff6fb7d00280a1 0x0afff6fb7d00280a 0x8fffffffc007c1f7 0xf8fffffffc007c1f

def z258 : W := mkw 0xc49ff097d497c000 0x0c49ff097d497c00 0x001ff007c007c002 0x0001ff007c007c00

def z259 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xf19f8fffc7c7ffff 0xff19f8fffc7c7fff

def z260 : W := mkw 0x7ffedf6abffffeaf 0x07ffedf6abffffea 0xffffffffffffffff 0xffffffffffffffff

def z261 : W := mkw 0x4940500021304000 0x0494050002130400 0x0060700000380000 0x0006070000038000

def z262 : W := mkw 0x9fff6fffca483e0e 0x09fff6fffca483e0 0x8fffffffc0003e07 0xf8fffffffc0003e0

def z263 : W := mkw 0x069f8cdf86c52948 0x8069f8cdf86c5294 0xdf9f8fffc7c739cf 0xfdf9f8fffc7c739c

def z264 : W := mkw 0x0414000010028000 0x0041400001002800 0x4e18000038030000 0x44e1800003803000

def z265 : W := mkw 0x0000004802402808 0x0000000480240280 0xd19809ff07c739cf 0x7d19809ff07c739c

def z266 : W := mkw 0x0b600f2008001400 0x00b600f200800140 0xefe00ff838003e0d 0xfefe00ff838003e0

def z267 : W := mkw 0x008b009500000000 0x0008b00950000000 0x018381f800000001 0x1018381f80000000

def z268 : W := mkw 0x2221bfc6ce1c77b5 0x42221bfc6ce1c77b 0xb067ffc7c63cffff 0xab067ffc7c63cfff

def z269 : W := mkw 0x9fff6fbfe9601c0a 0x09fff6fbfe9601c0 0xcffffffff9c01807 0xfcffffffff9c0180

def z270 : W := mkw 0x008b00dd02c12948 0x8008b00dd02c1294 0xc19809ff01c339c4 0x5c19809ff01c339c

def z271 : W := mkw 0x449fd0951497c140 0x8449fd0951497c14 0x001ff0070007c1c2 0x0001ff0070007c1c

def z272 : W := mkw 0x0b600f6802402808 0x00b600f680240280 0xdfe00ff807c0380d 0xfdfe00ff807c0380

def z273 : W := mkw 0x4000900025b54000 0x04000900025b5400 0x1000000007f80000 0x01000000007f8000

def z274 : W := mkw 0x0020330040184214 0x4002033004018421 0x0060700000380000 0x0006070000038000

def z275 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe40ffcfffcff3f 0xfffe40ffcfffcff3

def z276 : W := mkw 0x49cad00025b54000 0x049cad00025b5400 0x7fe3f0003ff80009 0xf7fe3f0003ff8000

def z277 : W := mkw 0x0b61bfe4461c6314 0x40b61bfe4461c631 0xbfe7fffcc63ce73f 0xfbfe7fffcc63ce73

def z278 : W := mkw 0x0000800004040000 0x0000080000404000 0x100380000604000b 0x2100380000604000

def z279 : W := mkw 0x0021b3cc46dd6b5c 0xc0021b3cc46dd6b5 0x7067f7c4c7ffffff 0xa7067f7c4c7fffff

def z280 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0x518381f807c739c9 0x1518381f807c739c

def z281 : W := mkw 0x0ddf409500000000 0x00ddf40950000000 0x8ffff9ff00000007 0xf8ffff9ff0000000

def z282 : W := mkw 0x00209340061c6204 0x000209340061c620 0x3067f7c0063ce60f 0xa3067f7c0063ce60

def z283 : W := mkw 0x0000904806dd6b5c 0xc0000904806dd6b5 0x7000000007fffff8 0x07000000007fffff

def z284 : W := mkw 0x008a900004954000 0x0008a90000495400 0x71fff00007ffc00b 0xf71fff00007ffc00

def z285 : W := mkw 0x9b612fffeb683e0e 0x09b612fffeb683e0 0xffe00ffffff83e0d 0xfffe00ffffff83e0

def z286 : W := mkw 0x49ca400021a10000 0x049ca400021a1000 0x0180000001c00000 0x10180000001c0000

def z287 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xcffffffff80318c7 0xfcffffffff80318c

def z288 : W := mkw 0x26343f02d81ad6b5 0x426343f02d81ad6b 0xee7c7e07f83ffffe 0xeee7c7e07f83ffff

def z289 : W := mkw 0x8ffffff7c61c6314 0x48ffffff7c61c631 0xbfffffffc63ce73f 0xfbfffffffc63ce73

def z290 : W := mkw 0x8fff7fb7c0184214 0x48fff7fb7c018421 0xafffffffc038c637 0xfafffffffc038c63

def z291 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0x118381fc07c4210f 0x3118381fc07c4210

def z292 : W := mkw 0x82000c3380000000 0x082000c338000000 0x8000083b00000000 0x08000083b0000000

def z293 : W := mkw 0x1b608f682fed3f4e 0x81b608f682fed3f4 0xffe00ff83fff3fcd 0xfffe00ff83fff3fc

def z294 : W := mkw 0x02200f2000000000 0x002200f200000000 0x80000ff800000004 0x080000ff80000000

def z295 : W := mkw 0x002123c442082314 0x4002123c44208231 0x200407c4c004e73e 0xa200407c4c004e73

def z296 : W := mkw 0x008b809504850000 0x0008b80950485000 0xd19b89ff07c7000f 0x7d19b89ff07c7000

def z297 : W := mkw 0x008a001100810040 0x8008a00110081004 0x00180003000300c0 0x000180003000300c

def z298 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8ffbf9fb00000001 0x58ffbf9fb0000000

def z299 : W := mkw 0x269e0c1b98c39ce9 0x8269e0c1b98c39ce 0xcf98083b39c318c0 0x5cf98083b39c318c

def z300 : W := mkw 0x6fdedc02bdb7d4a1 0x06fdedc02bdb7d4a 0x7ffff600ffffc63b 0xf7ffff600ffffc63

def z301 : W := mkw 0x1020036802482a0e 0x01020036802482a0 0x000001f800000000 0x0000001f80000000

def z302 : W := mkw 0x008a800004850000 0x0008a80000485000 0x1183800007c00001 0x11183800007c0000

def z303 : W := mkw 0x22000c02880014a1 0x022000c02880014a 0x80000e07c0003ff4 0x080000e07c0003ff

def z304 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xee1c0e03f803def0 0xcee1c0e03f803def

def z305 : W := mkw 0x02000c0008001400 0x002000c000800140 0x2e00060038000600 0x82e0006003800060

def z306 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x3fe7f0003ff8c001 0x93fe7f0003ff8c00

def z307 : W := mkw 0x4dde400031a38000 0x04dde400031a3800 0x6f9c000039c7c00a 0xf6f9c000039c7c00

def z308 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7f9800003fffc008 0x57f9800003fffc00

def z309 : W := mkw 0x0001b0c446146110 0x40001b0c44614611 0x1007f1c4c604e13f 0x21007f1c4c604e13

def z310 : W := mkw 0x8fffffb7c4144110 0x48fffffb7c414411 0x8fffffffc004c137 0xf8fffffffc004c13

def z311 : W := mkw 0x02000c480a403c08 0x002000c480a403c0 0xff800ff83fc03e0d 0xfff800ff83fc03e0

def z312 : W := mkw 0x00abb3dd46dd6b5c 0xc00abb3dd46dd6b5 0xd1fbf9ff07ff39cf 0x7d1fbf9ff07ff39c

def z313 : W := mkw 0x0000004802402808 0x0000000480240280 0x5000000007c03808 0x05000000007c0380

def z314 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0x501b800707c739ca 0x0501b800707c739c

def z315 : W := mkw 0x0001208440000000 0x0000120844000000 0x0007f004c0000002 0x00007f004c000000

def z316 : W := mkw 0x89ebf3f5461c6314 0x489ebf3f5461c631 0x11e3f1f806380001 0x111e3f1f80638000

def z317 : W := mkw 0x0940004823602808 0x0094000482360280 0xffe009f83ff8380d 0xfffe009f83ff8380

def z318 : W := mkw 0x22212fc6ca0837b5 0x422212fc6ca0837b 0x80000fc7c0003ff4 0x080000fc7c0003ff

def z319 : W := mkw 0xcdfff3b575b7c000 0x0cdfff3b575b7c00 0x7ffff1f83fffc00b 0xf7ffff1f83fffc00

def z320 : W := mkw 0x0021b384441c4314 0x40021b384441c431 0x2067f604c03cc732 0x82067f604c03cc73

def z321 : W := mkw 0x5ffedf203dbfd606 0x05ffedf203dbfd60 0x7ffff6003fffc60b 0xf7ffff6003fffc60

def z322 : W := mkw 0x269f8cdf9ec7bde9 0x8269f8cdf9ec7bde 0xdf9b89ff3fc739cf 0x7df9b89ff3fc739c

def z323 : W := mkw 0x1b609f682f7c7f1e 0x41b609f682f7c7f1 0xffe00ff83ffcff3d 0xfffe00ff83ffcff3

def z324 : W := mkw 0x20000000180294a1 0x020000000180294a 0x60040604f807fffe 0xa60040604f807fff

def z325 : W := mkw 0x8f746f22c0000000 0x08f746f22c000000 0x8e7c7e07c0000006 0xe8e7c7e07c000000

def z326 : W := mkw 0x0021a3c4460c2314 0x40021a3c4460c231 0x100387c4c604273f 0x2100387c4c604273

def z327 : W := mkw 0x2021b3c45e1ef7b5 0x42021b3c45e1ef7b 0x7067f7c4fe3fffff 0xa7067f7c4fe3ffff

def z328 : W := mkw 0x9fffffffef7c7f1e 0x49fffffffef7c7f1 0xfffffffffffcff3f 0xffffffffffffcff3

def z329 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19b89fb07c318c1 0x5d19b89fb07c318c

def z330 : W := mkw 0x008a805906c52948 0x8008a805906c5294 0xd198083b07c739c8 0x5d198083b07c739c

def z331 : W := mkw 0x8f756fb7c0000000 0x08f756fb7c000000 0x8e647fffc0000004 0x88e647fffc000000

def z332 : W := mkw 0x9fff6fffe3682a0e 0x09fff6fffe3682a0 0x9fffffffc7f80007 0xf9fffffffc7f8000

def z333 : W := mkw 0x89ebf3f5461c6314 0x489ebf3f5461c631 0x31e7f7fcc63ce73f 0xb31e7f7fcc63ce73

def z334 : W := mkw 0x002123dd42482b5c 0xc002123dd42482b5 0x80000fffc0003ff4 0x080000fffc0003ff

def z335 : W := mkw 0x82212fb7c0000000 0x082212fb7c000000 0x8067ffffc0000007 0xa8067ffffc000000

def z336 : W := mkw 0x86bf6fb7c0000000 0x086bf6fb7c000000 0x801fffffc0000006 0x0801fffffc000000

def z337 : W := mkw 0x49cad00035b7c000 0x049cad00035b7c00 0x71e3f0003fffc009 0x171e3f0003fffc00

def z338 : W := mkw 0x0000000000000000 0x0000000000000000 0x3060000006380009 0xa306000000638000

def z339 : W := mkw 0x000100dd02402948 0x8000100dd0240294 0xd18009ff07c039cd 0x7d18009ff07c039c

def z340 : W := mkw 0x008a801904c50848 0x8008a801904c5084 0xd19b883b07c718cb 0x7d19b883b07c718c

def z341 : W := mkw 0x000180cc06442908 0x0000180cc0644290 0xd18389fc07c4390f 0x7d18389fc07c4390

def z342 : W := mkw 0x0ddec00004850000 0x00ddec0000485000 0x5ffff00007c7000b 0xf5ffff00007c7000

def z343 : W := mkw 0x8dff63b540000000 0x08dff63b54000000 0x0ffff1f800000003 0xf0ffff1f80000000

def z344 : W := mkw 0x4414900035b7c000 0x04414900035b7c00 0x7e1c00003fffc00a 0xe7e1c00003fffc00

def z345 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xce180e07f8033ff4 0x4ce180e07f8033ff

def z346 : W := mkw 0x449ff0845497c110 0x4449ff0845497c11 0x001ff004c007c132 0x0001ff004c007c13

def z347 : W := mkw 0xefffffb7fdb7d4a1 0x0efffffb7fdb7d4a 0xffffffffffffffff 0xffffffffffffffff

def z348 : W := mkw 0x4dde500031b3c000 0x04dde500031b3c00 0x6ffc700039fbc000 0xd6ffc700039fbc00

def z349 : W := mkw 0x0021238440000000 0x0002123844000000 0x000007c4c0000004 0x0000007c4c000000

def z350 : W := mkw 0xaffffff7de1ef7b5 0x4affffff7de1ef7b 0xfffffffffe3fffff 0xffffffffffe3ffff

def z351 : W := mkw 0x00009040061c6314 0x400009040061c631 0x1000000006380000 0x0100000000638000

def z352 : W := mkw 0x6dded0003db7d4a1 0x06dded0003db7d4a 0x7ffff0003ffffffb 0xf7ffff0003ffffff

def z353 : W := mkw 0x1b603f2069385616 0x41b603f206938561 0x2e647600f838c630 0x82e647600f838c63

def z354 : W := mkw 0x849e401380000000 0x0849e40138000000 0x0018000300000000 0x0001800030000000

def z355 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xafffffffc004e73f 0xfafffffffc004e73

def z356 : W := mkw 0x06140c0280000000 0x006140c028000000 0xce1c0e07c00739ce 0xece1c0e07c00739c

def z357 : W := mkw 0x09cb80dd27e52948 0x809cb80dd27e5294 0xfffb89ff3fff39cf 0xffffb89ff3fff39c

def z358 : W := mkw 0x0020230040000000 0x0002023004000000 0x00647600c0000000 0x800647600c000000

def z359 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xee1808033807fff8 0x4ee1808033807fff

def z360 : W := mkw 0x9ffe4f7bab683e0e 0x09ffe4f7bab683e0 0xfff80ffb3ff83e0d 0xffff80ffb3ff83e0

def z361 : W := mkw 0x008a800004850000 0x0008a80000485000 0x001b800000070002 0x0001b80000007000

def z362 : W := mkw 0xcffeff22f5b7c000 0x0cffeff22f5b7c00 0x7ffff600ffffc00b 0xf7ffff600ffffc00

def z363 : W := mkw 0x449ed0001497c000 0x0449ed0001497c00 0x307ff000063fc00b 0xa307ff000063fc00

def z364 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x0e7ff607c0000002 0x80e7ff607c000000

def z365 : W := mkw 0x12200f2008081606 0x012200f200808160 0x0000060000000600 0x0000006000000060

def z366 : W := mkw 0x4000900035b7c000 0x04000900035b7c00 0x7067f0003fffc00b 0xa7067f0003fffc00

def z367 : W := mkw 0x249f80df96c7a9e9 0x8249f80df96c7a9e 0xd19f89ffc7c7f9ff 0x7d19f89ffc7c7f9f

def z368 : W := mkw 0xcddff097f5b7c000 0x0cddff097f5b7c00 0x7ffff007ffffc00b 0xf7ffff007ffffc00

def z369 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xcf800ff839c03e04 0x5cf800ff839c03e0

def z370 : W := mkw 0x408ad00004954000 0x0408ad0000495400 0x0003f00000000000 0x00003f0000000000

def z371 : W := mkw 0x1f740f6aab683e0e 0x01f740f6aab683e0 0xfffc0ffffff83e0f 0xffffc0ffffff83e0

def z372 : W := mkw 0x0dded00004144000 0x00dded0000414400 0x3ffff000063cc00b 0xf3ffff000063cc00

def z373 : W := mkw 0x8f746f22c0000000 0x08f746f22c000000 0x8fe47ff8c0000005 0xf8fe47ff8c000000

def z374 : W := mkw 0x12200f680a483e0e 0x012200f680a483e0 0xd1800ff807c03e0d 0x7d1800ff807c03e0

def z375 : W := mkw 0x0dde400010028000 0x00dde40001002800 0x6ffff0003807c00b 0xf6ffff0003807c00

def z376 : W := mkw 0x1b600f2029281606 0x01b600f202928160 0xafe00ff838380605 0xfafe00ff83838060

def z377 : W := mkw 0x5beadf682ffd7e0e 0x05beadf682ffd7e0 0xffe3fff83ff83e0d 0xfffe3fff83ff83e0

def z378 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x1067f7c4c6380007 0xa1067f7c4c638000

def z379 : W := mkw 0x4d5450003132c000 0x04d5450003132c00 0x7fe470003ff8c009 0xf7fe470003ff8c00

def z380 : W := mkw 0x0000004802402808 0x0000000480240280 0x118001f807c00001 0x1118001f807c0000

def z381 : W := mkw 0x80012097c0000000 0x080012097c000000 0x00000007c0000000 0x000000007c000000

def z382 : W := mkw 0x002123c442082314 0x4002123c44208231 0x306007c4c638273d 0xa306007c4c638273

def z383 : W := mkw 0x449fd0dd16d7e948 0x8449fd0dd16d7e94 0xd19ff9ff07c7f9cf 0x7d19ff9ff07c7f9c

def z384 : W := mkw 0x26352f86d80294a1 0x026352f86d80294a 0xee7fffc7f807ffff 0xeee7fffc7f807fff

def z385 : W := mkw 0x000190c406146100 0x0000190c40614610 0x3067f1c4063ce10f 0xa3067f1c4063ce10

def z386 : W := mkw 0x6f545c02b932d4a1 0x06f545c02b932d4a 0x2e647600f838c630 0x82e647600f838c63

def z387 : W := mkw 0x1ffe4f682b683e0e 0x01ffe4f682b683e0 0xfffffff83ff83e0f 0xffffffff83ff83e0

def z388 : W := mkw 0x0940900025344000 0x0094090002534400 0x7fe7f0003ffcc00b 0xf7fe7f0003ffcc00

def z389 : W := mkw 0x0414000010028000 0x0041400001002800 0x6e1c0604f807e73e 0xe6e1c0604f807e73

def z390 : W := mkw 0x008b809504850140 0x8008b80950485014 0x0003800000000000 0x0000380000000000

def z391 : W := mkw 0x1000000829601c0a 0x01000000829601c0 0x4000000039c01800 0x04000000039c0180

def z392 : W := mkw 0x200080481ec7bde9 0x8200080481ec7bde 0x700000003fc7fff8 0x0700000003fc7fff

def z393 : W := mkw 0x000100dd02402948 0x8000100dd0240294 0xc01809ff000739ce 0x6c01809ff000739c

def z394 : W := mkw 0x0021238440000000 0x0002123844000000 0x2067f7c4c004e73f 0xa2067f7c4c004e73

def z395 : W := mkw 0x12000c482b683e0e 0x012000c482b683e0 0xfe000e003ff83e0c 0xefe000e003ff83e0

def z396 : W := mkw 0x0ddfc0dd06c52948 0x80ddfc0dd06c5294 0xdffff9ff07c739cf 0xfdffff9ff07c739c

def z397 : W := mkw 0x3f75bfeeff7effbf 0x43f75bfeeff7effb 0xffffffffffffffff 0xffffffffffffffff

def z398 : W := mkw 0x1f740f683b6abe0e 0x01f740f683b6abe0 0xfffc0ff83ffffe0f 0xffffc0ff83ffffe0

def z399 : W := mkw 0x0000000000000000 0x0000000000000000 0x00180007000701c2 0x000180007000701c

def z400 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xae040e07f800fff4 0x8ae040e07f800fff

def z401 : W := mkw 0x008a000000000000 0x0008a00000000000 0x019b800000000003 0x7019b80000000000

def z402 : W := mkw 0xaf746f22d80294a1 0x0af746f22d80294a 0xee7c7e07f807fffe 0xeee7c7e07f807fff

def z403 : W := mkw 0x0dff638440000000 0x00dff63844000000 0x0ffff7c4c0000007 0xf0ffff7c4c000000

def z404 : W := mkw 0x000180c406042100 0x0000180c40604210 0x300787c4c604e73f 0xa300787c4c604e73

def z405 : W := mkw 0x8ffe6f22c0000000 0x08ffe6f22c000000 0x0ffff600c0000003 0xf0ffff600c000000

def z406 : W := mkw 0x5f745f20393ad606 0x05f745f20393ad60 0x2e6476003838c600 0x82e6476003838c60

def z407 : W := mkw 0x008a804806c52948 0x8008a804806c5294 0x519b800007c739cb 0x7519b800007c739c

def z408 : W := mkw 0x22010cdf8a403de9 0x822010cdf8a403de 0x80000fffc0003ff4 0x080000fffc0003ff

def z409 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3067f7c0c638c631 0x83067f7c0c638c63

def z410 : W := mkw 0x802123b540000000 0x0802123b54000000 0x000001f800000000 0x0000001f80000000

def z411 : W := mkw 0x12210ffd0a483f4e 0x812210ffd0a483f4 0x80000fff00003fc4 0x080000fff00003fc

def z412 : W := mkw 0x4ddfd09535b7c140 0x84ddfd09535b7c14 0x7ffff0073fffc1cb 0xf7ffff0073fffc1c

def z413 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3063f1c0063ce739 0x03063f1c0063ce73

def z414 : W := mkw 0x84146002c0000000 0x084146002c000000 0x00047000c0000000 0x000047000c000000

def z415 : W := mkw 0x0020334042186214 0x4002033404218621 0x306477c0c638e63d 0xa306477c0c638e63

def z416 : W := mkw 0x0001009500000140 0x8000100950000014 0x00000007000001c0 0x000000007000001c

def z417 : W := mkw 0x0940000021200000 0x0094000002120000 0x4f80000039c00000 0x54f80000039c0000

def z418 : W := mkw 0x0000000008001400 0x0000000000800140 0x6000000038003e08 0x06000000038003e0

def z419 : W := mkw 0x0414000000000000 0x0041400000000000 0x0e1c000000000002 0xe0e1c00000000000

def z420 : W := mkw 0x600090003db7d4a1 0x0600090003db7d4a 0x700000003ffffff8 0x0700000003ffffff

def z421 : W := mkw 0x0001808404040100 0x0000180840404010 0x0003800400040102 0x0000380040004010

def z422 : W := mkw 0x1960036823682a0e 0x01960036823682a0 0x31e007f807f8260d 0xb31e007f807f8260

def z423 : W := mkw 0x8fdfccff86c52948 0x88fdfccff86c5294 0xdf9b89ff07c739cf 0x7df9b89ff07c739c

def z424 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0xfffff8073ffff9cf 0xffffff8073ffff9c

def z425 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xae1c0e07f800c636 0xeae1c0e07f800c63

def z426 : W := mkw 0x8fff6fb7c8001400 0x08fff6fb7c800140 0xeffffffff8003e0f 0xfeffffffff8003e0

def z427 : W := mkw 0x008bb0dd46d56958 0xc008bb0dd46d5695 0xd19ff9ffc7c7f9ff 0x7d19ff9ffc7c7f9f

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0x00040604c0000006 0xa00040604c000000

def z429 : W := mkw 0x8fff6fffc2402808 0x08fff6fffc240280 0xdfffffffc7c0380f 0xfdfffffffc7c0380

def z430 : W := mkw 0x02000c0008001400 0x002000c000800140 0x80000e0000003e04 0x080000e0000003e0

def z431 : W := mkw 0x8f75ffe6c61c6314 0x48f75ffe6c61c631 0x3e67f7c4c63ce73f 0xa3e67f7c4c63ce73

def z432 : W := mkw 0x0000004002002000 0x0000000400200200 0x100001c00600200d 0x2100001c00600200

def z433 : W := mkw 0x4dde400031a38000 0x04dde400031a3800 0x7ff800003ffb0009 0xf7ff800003ffb000

def z434 : W := mkw 0x0414000010028000 0x0041400001002800 0x001c00000007c002 0x0001c00000007c00

def z435 : W := mkw 0x100000480a483e0e 0x0100000480a483e0 0x0000000000003e00 0x00000000000003e0

def z436 : W := mkw 0x049f80dd16c7a948 0x8049f80dd16c7a94 0xff9f89ff3fc7f9cf 0xfff9f89ff3fc7f9c

def z437 : W := mkw 0x4fdedc02b5b7c000 0x04fdedc02b5b7c00 0xfffffe07ffffc00f 0xffffffe07ffffc00

def z438 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xce1c0807f807d9f2 0x4ce1c0807f807d9f

def z439 : W := mkw 0x8fffffb7c4144000 0x08fffffb7c414400 0xbfffffffc63cc00f 0xfbfffffffc63cc00

def z440 : W := mkw 0xcfffffb7e5b54000 0x0cfffffb7e5b5400 0x9fffffffc7f80007 0xf9fffffffc7f8000

def z441 : W := mkw 0x1bea0f792be93e4e 0x81bea0f792be93e4 0xfff80ffb3ffb3ecd 0xffff80ffb3ffb3ec

def z442 : W := mkw 0x8ffffff7c61c6314 0x48ffffff7c61c631 0x9fffffffc6380007 0xf9fffffffc638000

def z443 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xcfffffffc00739cf 0xfcfffffffc00739c

def z444 : W := mkw 0x0000001900400848 0x8000000190040084 0x8000083b000018c0 0x08000083b000018c

def z445 : W := mkw 0x00aba3dd46c52948 0x800aba3dd46c5294 0xd1ffffffc7c739cf 0xfd1ffffffc7c739c

def z446 : W := mkw 0x408a900035b7c000 0x0408a900035b7c00 0x719b80003fffc00b 0x7719b80003fffc00

def z447 : W := mkw 0x0435b3c4561ee314 0x40435b3c4561ee31 0x7e7ff7c4fe3fe73f 0xe7e7ff7c4fe3fe73

def z448 : W := mkw 0x194000282160080a 0x0194000282160080 0x0180003801c00000 0x10180003801c0000

def z449 : W := mkw 0x9fffefffefed3f4e 0x89fffefffefed3f4 0xffffffffffff3fcf 0xfffffffffffff3fc

def z450 : W := mkw 0x0020034802482a0c 0x00020034802482a0 0xf1e00ff807f83e0d 0xff1e00ff807f83e0

def z451 : W := mkw 0x26150cdf9a42bde9 0x826150cdf9a42bde 0xee1c0ffff807fffe 0xeee1c0ffff807fff

def z452 : W := mkw 0x5dfed36837ffea0e 0x05dfed36837ffea0 0x7ffff1f83fffc00b 0xf7ffff1f83fffc00

def z453 : W := mkw 0x108b80dd2fed3f4e 0x8108b80dd2fed3f4 0xf19b89ff3fff3fcf 0x7f19b89ff3fff3fc

def z454 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0x918389ff07c039c5 0x1918389ff07c039c

def z455 : W := mkw 0x24140000180294a1 0x024140000180294a 0x6e1c00003807fffa 0xe6e1c00003807fff

def z456 : W := mkw 0x0020230040080214 0x4002023004008021 0x00000600c0000630 0x000000600c000063

def z457 : W := mkw 0x1bca0c3929e11c4a 0x81bca0c3929e11c4 0xcf98083b39c318c0 0x5cf98083b39c318c

def z458 : W := mkw 0x441450001012c000 0x0441450001012c00 0x000470000000c000 0x0000470000000c00

def z459 : W := mkw 0x22000c02880014a1 0x022000c02880014a 0x00000600c0000630 0x000000600c000063

def z460 : W := mkw 0xcfff7fb7f132c000 0x0cfff7fb7f132c00 0xaffffffff838c007 0xfaffffffff838c00

def z461 : W := mkw 0x06140c0290028000 0x006140c029002800 0xee1c0e07f807c00e 0xeee1c0e07f807c00

def z462 : W := mkw 0x0000900004144000 0x0000090000414400 0x0007f0000004c002 0x00007f0000004c00

def z463 : W := mkw 0x02200f400a083604 0x002200f400a08360 0xfe600fc03e383e0d 0xefe600fc03e383e0

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x5180000007c00009 0x75180000007c0000

def z465 : W := mkw 0x3fff8fffbfefbfef 0x83fff8fffbfefbfe 0xffff8fffffffffff 0xfffff8ffffffffff

def z466 : W := mkw 0x000100dd02402948 0x8000100dd0240294 0x000001f800000000 0x0000001f80000000

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x6e00000038000008 0xe6e0000003800000

def z468 : W := mkw 0x1b618fec2f6c3f0e 0x01b618fec2f6c3f0 0xffe38ffc3ffc3f0f 0xfffe38ffc3ffc3f0

def z469 : W := mkw 0x5fffffec7fffff1e 0x45fffffec7fffff1 0xfffffffcffffff3f 0xffffffffcffffff3

def z470 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000004e738 0x0200000000004e73

def z471 : W := mkw 0x0021b3cc465c6b1c 0x40021b3cc465c6b1 0xf1e7fffcc7fcff3f 0xff1e7fffcc7fcff3

def z472 : W := mkw 0x008b009500000000 0x0008b00950000000 0x001b800700000002 0x0001b80070000000

def z473 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0x801c0e07c007fff6 0x0801c0e07c007fff

def z474 : W := mkw 0x4dded0001497c000 0x04dded0001497c00 0x0ffff0000007c003 0xf0ffff0000007c00

def z475 : W := mkw 0x0dfff3c4461c6314 0x40dfff3c4461c631 0x3ffff7c4c63ce73f 0xf3ffff7c4c63ce73

def z476 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0x91e00ff807f83e05 0x191e00ff807f83e0

def z477 : W := mkw 0x649ed0029497c0a1 0x0649ed0029497c0a 0x001ff007c007c1f2 0x0001ff007c007c1f

def z478 : W := mkw 0x00ab83dd06cd2b4c 0x800ab83dd06cd2b4 0xf1fb8fff07ff3fcf 0xff1fb8fff07ff3fc

def z479 : W := mkw 0x82ab2fb7c0000000 0x082ab2fb7c000000 0x819b8fffc0000007 0x7819b8fffc000000

def z480 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0x6e040600f807fff8 0x86e040600f807fff

def z481 : W := mkw 0xafff6fb7c80014a1 0x0afff6fb7c80014a 0x8fffffffc0003ff7 0xf8fffffffc0003ff

def z482 : W := mkw 0x49ebf3c467bd6314 0x449ebf3c467bd631 0x11e3f1c007f80001 0x111e3f1c007f8000

def z483 : W := mkw 0x82202f22c0000000 0x082202f22c000000 0x00000600c0000000 0x000000600c000000

def z484 : W := mkw 0x008a001100000000 0x0008a00110000000 0x8198083b00000000 0x58198083b0000000

def z485 : W := mkw 0x8fff6ff7c2082204 0x08fff6ff7c208220 0xbfffffffc638260f 0xfbfffffffc638260

def z486 : W := mkw 0x5f745f683b7afe0e 0x05f745f683b7afe0 0xffe47ff83ff8fe0d 0xfffe47ff83ff8fe0

def z487 : W := mkw 0x1960036823682a0e 0x01960036823682a0 0x7fe001f83ff80009 0xf7fe001f83ff8000

def z488 : W := mkw 0xafffefffdec7bde9 0x8afffefffdec7bde 0xffffffffffc7ffff 0xfffffffffffc7fff

def z489 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xae600ff838383e04 0x8ae600ff838383e0

def z490 : W := mkw 0x26352fc6da0ab7b5 0x426352fc6da0ab7b 0xee1c0fc7f807fffe 0xeee1c0fc7f807fff

def z491 : W := mkw 0x12200f680a483e0e 0x012200f680a483e0 0xb0600ff806383e0d 0xab0600ff806383e0

def z492 : W := mkw 0x000190c4061c6314 0x4000190c4061c631 0x300381c4063ce73f 0x2300381c4063ce73

def z493 : W := mkw 0x99eb63fd63682a0e 0x099eb63fd63682a0 0x11e3f1f807f80001 0x111e3f1f807f8000

def z494 : W := mkw 0x89ebe3fd46c52948 0x889ebe3fd46c5294 0xd1fbf9ff07c739cf 0x7d1fbf9ff07c739c

def z495 : W := mkw 0x0414000280000000 0x0041400028000000 0x001c0007c0000002 0x0001c0007c000000

def z496 : W := mkw 0x8beb6fb540000000 0x08beb6fb54000000 0x8fe3fff800000005 0xf8fe3fff80000000

def z497 : W := mkw 0x1b610ffd2b683f4e 0x81b610ffd2b683f4 0xffe00fff3ff83fcd 0xfffe00fff3ff83fc

def z498 : W := mkw 0x00009040061c6314 0x400009040061c631 0x3067f000063ce73b 0xa3067f000063ce73

def z499 : W := mkw 0x00abb3c4469d6314 0x400abb3c4469d631 0x71fff7c4c7ffe73f 0xf71fff7c4c7ffe73

def z500 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0x119b81ff07c701c3 0x1119b81ff07c701c

def z501 : W := mkw 0x8fffeff7c6042100 0x08fffeff7c604210 0x9fffffffc604210f 0xf9fffffffc604210

def z502 : W := mkw 0x6fffffc6ffbff7b5 0x46fffffc6ffbff7b 0xffffffc7ffffffff 0xfffffffc7fffffff

def z503 : W := mkw 0x06140c0280000000 0x006140c028000000 0x8e18080300000000 0x48e1808030000000

def z504 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0x6e1c0600f807c63a 0xe6e1c0600f807c63

def z505 : W := mkw 0x6f545c02b932d4a1 0x06f545c02b932d4a 0xee7c7e07f83ffffe 0xeee7c7e07f83ffff

def z506 : W := mkw 0x24140002980294a1 0x024140002980294a 0x601c0007f807fffa 0x0601c0007f807fff

def z507 : W := mkw 0x1961b3ec677c6b1e 0x41961b3ec677c6b1 0x11e3f1f807f80001 0x111e3f1f807f8000

def z508 : W := mkw 0x24140002900280a1 0x024140002900280a 0x00180003000300c0 0x000180003000300c

def z509 : W := mkw 0x449e400010838000 0x0449e40001083800 0x0018000000030000 0x0001800000003000

def z510 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x0007f7c4c004e736 0x00007f7c4c004e73

def z511 : W := mkw 0x1b600f602b283606 0x01b600f602b28360 0x3e6007c03e38260d 0xa3e6007c03e38260

def z512 : W := mkw 0x5fdedc283df7dc0a 0x05fdedc283df7dc0 0xfffff8383fffd80b 0xffffff8383fffd80

def z513 : W := mkw 0x19eb83fd27ed2b4e 0x819eb83fd27ed2b4 0x11e381f807f80001 0x111e381f807f8000

def z514 : W := mkw 0x100080482fed3f4e 0x8100080482fed3f4 0x700000003fff3fc8 0x0700000003fff3fc

def z515 : W := mkw 0x26140c02900280a1 0x026140c02900280a 0x8e1c0e07c007c1f6 0xe8e1c0e07c007c1f

def z516 : W := mkw 0x00ab239540000000 0x000ab23954000000 0x81ffffffc0000007 0xf81ffffffc000000

def z517 : W := mkw 0x8fff6fbfc0c10848 0x88fff6fbfc0c1084 0xcfffffffc1c318c7 0xfcfffffffc1c318c

def z518 : W := mkw 0x5dded0483ffffe0e 0x05dded0483ffffe0 0x7ffff0003ffffe0b 0xf7ffff0003ffffe0

def z519 : W := mkw 0x041490001416c000 0x0041490001416c00 0x7e7ff0003e3fc00b 0xe7e7ff0003e3fc00

def z520 : W := mkw 0x4000000031a38000 0x04000000031a3800 0x4000000039c30000 0x04000000039c3000

def z521 : W := mkw 0x0b600f6002082204 0x00b600f600208220 0xbfe00ff80638260d 0xfbfe00ff80638260

def z522 : W := mkw 0x00abb3d5469d6354 0xc00abb3d5469d635 0x307ff7c7c63fe7ff 0xa307ff7c7c63fe7f

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0x401800000007000a 0x6401800000007000

def z524 : W := mkw 0x0000100000104000 0x0000010000010400 0x206470000038c000 0x8206470000038c00

def z525 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xce1c0e07f80318c6 0xece1c0e07f80318c

def z526 : W := mkw 0x0414000010028000 0x0041400001002800 0xee1c08073807f9ce 0xeee1c08073807f9c

def z527 : W := mkw 0x0940000021200000 0x0094000002120000 0x11e0000007f80001 0x111e0000007f8000

def z528 : W := mkw 0x008b90dd06d56948 0x8008b90dd06d5694 0xf1fff9ff07fff9cf 0xff1fff9ff07fff9c

def z529 : W := mkw 0x400010003132c000 0x0400010003132c00 0x200000003838c000 0x0200000003838c00

def z530 : W := mkw 0x4ddfd09535b7c000 0x04ddfd09535b7c00 0xfffff9ff3fffc00f 0xffffff9ff3fffc00

def z531 : W := mkw 0x0020034002082204 0x0002003400208220 0x306407c4c63ce73f 0xa306407c4c63ce73

def z532 : W := mkw 0x300000483b6abeaf 0x0300000483b6abea 0x700000003ffffff8 0x0700000003ffffff

def z533 : W := mkw 0x84bff3d7c61c6314 0x484bff3d7c61c631 0x307ff7c7c63ce73f 0xa307ff7c7c63ce73

def z534 : W := mkw 0x1b600f2829681e0e 0x01b600f2829681e0 0xefe00e3839f81e00 0xdefe00e3839f81e0

def z535 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0x0e00000038000000 0x00e0000003800000

def z536 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xee1c08033807d8ca 0xeee1c08033807d8c

def z537 : W := mkw 0x049e400000000000 0x0049e40000000000 0x001ff00000000002 0x0001ff0000000000

def z538 : W := mkw 0x00209340061c6314 0x400209340061c631 0x306007c0063ce73d 0xa306007c0063ce73

def z539 : W := mkw 0x1bebbffd6ffd7f5e 0xc1bebbffd6ffd7f5 0xffffffffffffffff 0xffffffffffffffff

def z540 : W := mkw 0x4dfff3dd77ffeb5c 0xc4dfff3dd77ffeb5 0xffffffffffffffff 0xffffffffffffffff

def z541 : W := mkw 0x8fdf6cb7c0000000 0x08fdf6cb7c000000 0x8f9ff83fc0000002 0x58f9ff83fc000000

def z542 : W := mkw 0x2615bc86dc16d5b1 0x42615bc86dc16d5b 0xee1ffe07f807fffe 0xeee1ffe07f807fff

def z543 : W := mkw 0x0beb8ffd06c52948 0x80beb8ffd06c5294 0xdffb8fff07c739cf 0xfdffb8fff07c739c

def z544 : W := mkw 0x4dfff3c477bfe314 0x44dfff3c477bfe31 0x7ffff1c03fffc00b 0xf7ffff1c03fffc00

def z545 : W := mkw 0x0020030000080204 0x0002003000008020 0x2060060000380600 0x8206006000038060

def z546 : W := mkw 0x0940000021200000 0x0094000002120000 0x2e60000038380000 0x82e6000003838000

def z547 : W := mkw 0x008b80d506852140 0x8008b80d50685214 0x101b81c7060721cf 0x2101b81c7060721c

def z548 : W := mkw 0x4940900035b7c000 0x04940900035b7c00 0x7fe000003fffc009 0xf7fe000003fffc00

def z549 : W := mkw 0x5b609f683ffffe0e 0x05b609f683ffffe0 0xffe00ff83ffffe0d 0xfffe00ff83ffffe0

def z550 : W := mkw 0x008bb09544954150 0xc008bb0954495415 0x001ff007c007c1f2 0x0001ff007c007c1f

def z551 : W := mkw 0x1000004823682a0e 0x01000004823682a0 0x1000000007f80000 0x01000000007f8000

def z552 : W := mkw 0x6fdedc02bdb7d4a1 0x06fdedc02bdb7d4a 0xfffff8033fffd8cb 0xffffff8033fffd8c

def z553 : W := mkw 0x4d747300713ac214 0x44d747300713ac21 0x2e647600f838c630 0x82e647600f838c63

def z554 : W := mkw 0x1b612fec6b683f1e 0x41b612fec6b683f1 0xffe00ffcfff83f3d 0xfffe00ffcfff83f3

def z555 : W := mkw 0x849f6097c0000000 0x0849f6097c000000 0x819ff9ffc0000007 0x7819ff9ffc000000

def z556 : W := mkw 0x0000900004144000 0x0000090000414400 0x1063f00006380001 0x01063f0000638000

def z557 : W := mkw 0x002123c442082314 0x4002123c44208231 0x000001c000000000 0x0000001c00000000

def z558 : W := mkw 0x069f0c9780000000 0x0069f0c978000000 0x8f9f8fffc0000007 0xf8f9f8fffc000000

def z559 : W := mkw 0x12200f680a483e0e 0x012200f680a483e0 0xee000ff838003e0c 0xeee000ff838003e0

def z560 : W := mkw 0x86352fb7c0000000 0x086352fb7c000000 0x8e1c0fffc0000006 0xe8e1c0fffc000000

def z561 : W := mkw 0x4dfff38475b7c000 0x04dfff38475b7c00 0x7ffff7c4ffffc00f 0xf7ffff7c4ffffc00

def z562 : W := mkw 0x1b600f2029281606 0x01b600f202928160 0x7fe006003ff80609 0xf7fe006003ff8060

def z563 : W := mkw 0x66149c02bdb7d4a1 0x066149c02bdb7d4a 0xfe1c0e07fffffffe 0xefe1c0e07fffffff

def z564 : W := mkw 0x3f740f6abb6abeaf 0x03f740f6abb6abea 0xfff80ffb3ffb3ecd 0xffff80ffb3ffb3ec

def z565 : W := mkw 0x008b809d04c50948 0x8008b809d04c5094 0xc19b883f01c719c2 0x5c19b883f01c719c

def z566 : W := mkw 0x0001208440000110 0x4000120844000011 0x00000004c0000130 0x000000004c000013

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000807000039c4 0x080000807000039c

def z568 : W := mkw 0x00abb3dd46dd6b5c 0xc00abb3dd46dd6b5 0x11e3f1f807f80001 0x111e3f1f807f8000

def z569 : W := mkw 0x002133c442186314 0x4002133c44218631 0x206477c4c038e734 0x8206477c4c038e73

def z570 : W := mkw 0x00aba3dd46cd2b5c 0xc00aba3dd46cd2b5 0xd19b8fffc7c73fff 0x7d19b8fffc7c73ff

def z571 : W := mkw 0x028b8cdd0ec53d48 0x8028b8cdd0ec53d4 0xff9b8fff3fc73fcf 0xfff9b8fff3fc73fc

def z572 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xce180807380739ce 0x6ce180807380739c

def z573 : W := mkw 0x1bea8f682fed3e0e 0x01bea8f682fed3e0 0xfffb8ff83fff3e0f 0xffffb8ff83fff3e0

def z574 : W := mkw 0x20000000080014a1 0x020000000080014a 0x0000000000003ff0 0x00000000000003ff

def z575 : W := mkw 0x8fffffffc6dd6b5c 0xc8fffffffc6dd6b5 0xffffffffc7ffffff 0xfffffffffc7fffff

def z576 : W := mkw 0x8fffefffc6c52948 0x88fffefffc6c5294 0x9fffffffc7c00007 0xf9fffffffc7c0000

def z577 : W := mkw 0x4d75f3c4773ee314 0x44d75f3c4773ee31 0x3e67f7c4fe3ce73f 0xa3e67f7c4fe3ce73

def z578 : W := mkw 0x1021b3cc6f7c7f1e 0x41021b3cc6f7c7f1 0x7067f7c4fffcff3f 0xa7067f7c4fffcff3

def z579 : W := mkw 0x000100c402002100 0x0000100c40200210 0x000001c400002104 0x0000001c40000210

def z580 : W := mkw 0x4dded01935f7c848 0x84dded01935f7c84 0xfffff83b3fffd8cb 0xffffff83b3fffd8c

def z581 : W := mkw 0xa69f6c97d80294a1 0x0a69f6c97d80294a 0xee1ffe07f807fffe 0xeee1ffe07f807fff

def z582 : W := mkw 0x008a001900c10848 0x8008a001900c1084 0xc198083f01c739ce 0x7c198083f01c739c

def z583 : W := mkw 0x1b600f2829601c0a 0x01b600f2829601c0 0xcfe00ff839c01805 0xfcfe00ff839c0180

def z584 : W := mkw 0x06140c0288001400 0x006140c028800140 0xee1c0e07f8003e0e 0xeee1c0e07f8003e0

def z585 : W := mkw 0x449ed00035b7c000 0x0449ed00035b7c00 0x701ff0003fffc00a 0x0701ff0003fffc00

def z586 : W := mkw 0x1b609f682f7c7e0e 0x01b609f682f7c7e0 0xffe7fff83ffcfe0f 0xfffe7fff83ffcfe0

def z587 : W := mkw 0x8fffefb7c4850140 0x88fffefb7c485014 0x8fffffffc00701c7 0xf8fffffffc00701c

def z588 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3063f7c00638260d 0xa3063f7c00638260

def z589 : W := mkw 0x8ffe6f33c0000000 0x08ffe6f33c000000 0x8ffc7e3bc0000000 0xd8ffc7e3bc000000

def z590 : W := mkw 0x008b809504850140 0x8008b80950485014 0x519b800707c701cb 0x7519b800707c701c

def z591 : W := mkw 0x269f8c979c8795e1 0x8269f8c979c8795e 0xee1f8e07f807fffe 0xeee1f8e07f807fff

def z592 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xee180e0338033ecc 0xeee180e0338033ec

def z593 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd18389f807c0380d 0x7d18389f807c0380

def z594 : W := mkw 0x9f746f22e9281606 0x09f746f22e928160 0x2e647600f8380600 0x82e647600f838060

def z595 : W := mkw 0xc9ebf3b565b54000 0x0c9ebf3b565b5400 0x11e3f1f807f80001 0x111e3f1f807f8000

def z596 : W := mkw 0x269e0c1b98c39ce9 0x8269e0c1b98c39ce 0xef9c0e3ff9c7fffe 0xfef9c0e3ff9c7fff

def z597 : W := mkw 0x2415b086d416c1b1 0x42415b086d416c1b 0x001ff007c007c1f2 0x0001ff007c007c1f

def z598 : W := mkw 0x22000c02880014a1 0x022000c02880014a 0xee000e07f8003ffc 0xeee000e07f8003ff

def z599 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x1063f7c4c6382735 0x01063f7c4c638273

def z600 : W := mkw 0x0000300040104010 0x4000030004010401 0x00047000c000c030 0x000047000c000c03

def z601 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0x2e040604f804e73e 0xa2e040604f804e73

def z602 : W := mkw 0x000180c406042100 0x0000180c40604210 0xd01b89c7060739cf 0x6d01b89c7060739c

def z603 : W := mkw 0x1960032021280206 0x0196003202128020 0x0060000000380000 0x0006000000038000

def z604 : W := mkw 0x0021338440184214 0x4002133844018421 0x2067f7c4c038c637 0xa2067f7c4c038c63

def z605 : W := mkw 0x0961b3c4673c6314 0x40961b3c4673c631 0x7fe7f7c4fffce73f 0xf7fe7f7c4fffce73

def z606 : W := mkw 0x0000004802402808 0x0000000480240280 0x800009f800003804 0x0800009f80000380

def z607 : W := mkw 0x1960036823682a0e 0x01960036823682a0 0xd1e009f807f8380d 0x7d1e009f807f8380

def z608 : W := mkw 0x06140c0280000000 0x006140c028000000 0x0e040600c0000000 0x80e040600c000000

def z609 : W := mkw 0x20000000180294a1 0x020000000180294a 0x200000003800c630 0x0200000003800c63

def z610 : W := mkw 0x49cbd0dd27f56948 0x849cbd0dd27f5694 0x11e3f1f807f80001 0x111e3f1f807f8000

def z611 : W := mkw 0x0021b38444144000 0x00021b3844414400 0x3067f7c4c63cc00f 0xa3067f7c4c63cc00

def z612 : W := mkw 0x26340f429a0ab6a5 0x026340f429a0ab6a 0xfe7c0fc7fe3fffff 0xefe7c0fc7fe3ffff

def z613 : W := mkw 0x4ddfc0dd37e7a948 0x84ddfc0dd37e7a94 0xdf9b89ff3fc739cf 0x7df9b89ff3fc739c

def z614 : W := mkw 0x5ffe4f683bebbe0e 0x05ffe4f683bebbe0 0xfff80ff83ffb3e0d 0xffff80ff83ffb3e0

def z615 : W := mkw 0x408b90dd37f7e948 0x8408b90dd37f7e94 0xf19b89ff3ffff9cf 0x7f19b89ff3ffff9c

def z616 : W := mkw 0x4ddec00035a78000 0x04ddec00035a7800 0x5f9b80003fc7000b 0x75f9b80003fc7000

def z617 : W := mkw 0x0b400c0029201400 0x00b400c002920140 0xffe00e003ff83e0d 0xfffe00e003ff83e0

def z618 : W := mkw 0x0414000010028000 0x0041400001002800 0x2e0400003800c000 0x82e0400003800c00

def z619 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8f980fffc0000004 0x58f980fffc000000

def z620 : W := mkw 0x0d54000031228000 0x00d5400003122800 0x7ffc00003fffc00b 0xf7ffc00003fffc00

def z621 : W := mkw 0x2fde4c02980294a1 0x02fde4c02980294a 0xeffffe07f807ffff 0xfeffffe07f807fff

def z622 : W := mkw 0x194000482b683e0e 0x0194000482b683e0 0x7fe000003ff83e09 0xf7fe000003ff83e0

def z623 : W := mkw 0x4dded00025b54000 0x04dded00025b5400 0x1ffff00007f80003 0xf1ffff00007f8000

def z624 : W := mkw 0x0000100000184214 0x4000010000018421 0x200000000038c630 0x0200000000038c63

def z625 : W := mkw 0x06352f86c0000000 0x006352f86c000000 0x8e7fffc7c0000007 0xe8e7fffc7c000000

def z626 : W := mkw 0x8fde4c3b80c10848 0x88fde4c3b80c1084 0xcf98083b01c318c0 0x5cf98083b01c318c

def z627 : W := mkw 0x4ffedf2035b7c000 0x04ffedf2035b7c00 0xfffffff83fffc00f 0xffffffff83fffc00

def z628 : W := mkw 0x49ebf3c467bd6314 0x449ebf3c467bd631 0x31e7f7c4c7fce73f 0xb31e7f7c4c7fce73

def z629 : W := mkw 0x1b600f680a483e0e 0x01b600f680a483e0 0x8fe00ff800003e05 0xf8fe00ff800003e0

def z630 : W := mkw 0x4dfed34037bfe204 0x04dfed34037bfe20 0x7ffff7c03fffe60f 0xf7ffff7c03fffe60

def z631 : W := mkw 0x06140c0280000000 0x006140c028000000 0xae1c0e07c004e73e 0xeae1c0e07c004e73

def z632 : W := mkw 0x8f747f22c0184214 0x48f747f22c018421 0x2e647600c038c630 0x82e647600c038c63

def z633 : W := mkw 0x0fde4c0280000000 0x00fde4c028000000 0x8ffffe07c0000007 0xf8ffffe07c000000

def z634 : W := mkw 0x8221bff7c61c6314 0x48221bff7c61c631 0xb067ffffc63ce73f 0xab067ffffc63ce73

def z635 : W := mkw 0x0000900004144000 0x0000090000414400 0x30000000063cc008 0x030000000063cc00

def z636 : W := mkw 0x0020034002082204 0x0002003400208220 0x000007c000002604 0x0000007c00000260

def z637 : W := mkw 0x1961b3ec677c6b1e 0x41961b3ec677c6b1 0x31e7f7fcc7fce73f 0xb31e7f7fcc7fce73

def z638 : W := mkw 0x26bfbfdfdedffffd 0xc26bfbfdfdedffff 0xffffffffffffffff 0xffffffffffffffff

def z639 : W := mkw 0x0000000800400808 0x0000000080040080 0xc180083801c01800 0x5c180083801c0180

def z640 : W := mkw 0x12ab8ffd0ecd3f4e 0x812ab8ffd0ecd3f4 0xd19b8fff07c73fcf 0x7d19b8fff07c73fc

def z641 : W := mkw 0x0000000000000000 0x0000000000000000 0xe01c0e07c007fffe 0xee01c0e07c007fff

def z642 : W := mkw 0x1beb8ffd2fed3f4e 0x81beb8ffd2fed3f4 0xffe38ff83ff83e0d 0xfffe38ff83ff83e0

def z643 : W := mkw 0x49cad00025b54000 0x049cad00025b5400 0x51fbf00007ff000b 0x751fbf00007ff000

def z644 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0x519b81f807c7000b 0x7519b81f807c7000

def z645 : W := mkw 0x0001b0c4461c6314 0x40001b0c4461c631 0x3007f004c63ce73a 0x03007f004c63ce73

def z646 : W := mkw 0x02000c0008001400 0x002000c000800140 0xce00080038001800 0x4ce0008003800180

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000604c0002734 0x000000604c000273

def z648 : W := mkw 0x22000c02880014a1 0x022000c02880014a 0x80000803000018c0 0x080000803000018c

def z649 : W := mkw 0x3f740f6abb6abeaf 0x03f740f6abb6abea 0xffe40ff8fff8fe3d 0xfffe40ff8fff8fe3

def z650 : W := mkw 0x1b400c682b683e0e 0x01b400c682b683e0 0xff8008383ff83e08 0x5ff8008383ff83e0

def z651 : W := mkw 0x20000000180294a1 0x020000000180294a 0xe01808073807fffe 0x6e01808073807fff

def z652 : W := mkw 0x4ddfd0c437b7e100 0x04ddfd0c437b7e10 0x7ffff1c43fffe10f 0xf7ffff1c43fffe10

def z653 : W := mkw 0x0020030000000000 0x0002003000000000 0x006007c000000005 0xa006007c00000000

def z654 : W := mkw 0x26149c029c16d4a1 0x026149c029c16d4a 0xfe7ffe07fe3fffff 0xefe7ffe07fe3ffff

def z655 : W := mkw 0x0001009500000000 0x0000100950000000 0x800009ff00000004 0x0800009ff0000000

def z656 : W := mkw 0x0000000021200000 0x0000000002120000 0x700000003ff80008 0x0700000003ff8000

def z657 : W := mkw 0x02000c0008001400 0x002000c000800140 0xee180e0738073fce 0xeee180e0738073fc

def z658 : W := mkw 0x0beb0fb500000000 0x00beb0fb50000000 0x8ffb8fff00000007 0xf8ffb8fff0000000

def z659 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x1067f1c4c63cc133 0x01067f1c4c63cc13

def z660 : W := mkw 0x008a005902c12848 0x8008a005902c1284 0xd19809fb07c338cd 0x7d19809fb07c338c

def z661 : W := mkw 0x249f8097948781e1 0x8249f8097948781e 0x001f8007c007c1f2 0x0001f8007c007c1f

def z662 : W := mkw 0x22000c02880014a1 0x022000c02880014a 0xc0180e07c0073ffe 0x6c0180e07c0073ff

def z663 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0x7e6006003ff83e08 0x87e6006003ff83e0

def z664 : W := mkw 0x000180c406042100 0x0000180c40604210 0x100381c006000001 0x0100381c00600000

def z665 : W := mkw 0x2f740f22980294a1 0x02f740f22980294a 0xeffc0ffff807ffff 0xfeffc0ffff807fff

def z666 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x2e7ff000383fc002 0x82e7ff000383fc00

def z667 : W := mkw 0x20000002800000a1 0x020000002800000a 0x00000007c00001f0 0x000000007c00001f

def z668 : W := mkw 0x008b00dd02402808 0x0008b00dd0240280 0xd19b89ff07c0380f 0x7d19b89ff07c0380

def z669 : W := mkw 0x1b603f686b787e1e 0x41b603f686b787e1 0xffe47ff8fff8fe3d 0xfffe47ff8fff8fe3

def z670 : W := mkw 0x0021a3c446042100 0x00021a3c44604210 0x1067f7c4c604210f 0xa1067f7c4c604210

def z671 : W := mkw 0x3f540c2ab9629cab 0x03f540c2ab9629ca 0xcf98083b39c318c0 0x5cf98083b39c318c

def z672 : W := mkw 0x0001b08444144110 0x40001b0844414411 0x2007f604c004e73e 0xa2007f604c004e73

def z673 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0x801b89ff000739c6 0x0801b89ff000739c

def z674 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fe0000000000001 0xf0fe000000000000

def z675 : W := mkw 0x12000c2808401c0a 0x012000c2808401c0 0x8000083800001800 0x0800008380000180

def z676 : W := mkw 0x849fe097c4850140 0x8849fe097c485014 0x001ff007c00701c2 0x0001ff007c00701c

def z677 : W := mkw 0x0000000010028000 0x0000000001002800 0x600000003807c008 0x0600000003807c00

def z678 : W := mkw 0x008a800004850000 0x0008a80000485000 0xd19b880707c739cf 0x7d19b880707c739c

def z679 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x300007c4c63ce73c 0x0300007c4c63ce73

def z680 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00008000000380c 0x6c00008000000380

def z681 : W := mkw 0x0020b340461c6314 0x40020b340461c631 0x30647600c63ce738 0x830647600c63ce73

def z682 : W := mkw 0x4fdedc003db7d400 0x04fdedc003db7d40 0xfffffe003ffffe0f 0xffffffe003ffffe0

def z683 : W := mkw 0x0f740f2280000000 0x00f740f228000000 0x8ffc0fffc0000007 0xf8ffc0fffc000000

def z684 : W := mkw 0x669edc029c97d4a1 0x0669edc029c97d4a 0xee1ffe07f807fffe 0xeee1ffe07f807fff

def z685 : W := mkw 0x0635bfc6c61c6314 0x40635bfc6c61c631 0xbe7fffc7c63ce73f 0xebe7fffc7c63ce73

def z686 : W := mkw 0x06140c0018029400 0x006140c001802940 0xee1c0e003807fe0e 0xeee1c0e003807fe0

def z687 : W := mkw 0xcfde4c33b1a38000 0x0cfde4c33b1a3800 0xcf98083b39c30000 0x5cf98083b39c3000

def z688 : W := mkw 0x0021b38444144110 0x40021b3844414411 0x0067f7c4c004c137 0xa0067f7c4c004c13

def z689 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x4f9ff00039c7c002 0x54f9ff00039c7c00

def z690 : W := mkw 0x00abb3dd46dd6b5c 0xc00abb3dd46dd6b5 0x31e7f7fcc7fce73f 0xb31e7f7fcc7fce73

def z691 : W := mkw 0x0000804006042100 0x0000080400604210 0x1000000006042108 0x0100000000604210

def z692 : W := mkw 0x1b600f2029281606 0x01b600f202928160 0xee600e0038383e0c 0xeee600e0038383e0

def z693 : W := mkw 0xa6352fb7d80294a1 0x0a6352fb7d80294a 0xee1c0ffff807fffe 0xeee1c0ffff807fff

def z694 : W := mkw 0x1b400c2029201402 0x01b400c202920140 0x0e00000038000000 0x00e0000003800000

def z695 : W := mkw 0x20000000100280a1 0x020000000100280a 0x000000000007c1f0 0x0000000000007c1f

def z696 : W := mkw 0x4d54d0003536c000 0x04d54d0003536c00 0x3e67f0003e3cc00b 0xa3e67f0003e3cc00

def z697 : W := mkw 0x0000804806c52948 0x80000804806c5294 0xd18009f807c739cd 0x7d18009f807c739c

def z698 : W := mkw 0x1b400c682b603c0a 0x01b400c682b603c0 0xdf8009f83fc0380d 0x7df8009f83fc0380

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x20040600c000c630 0x820040600c000c63

def z700 : W := mkw 0x0b400c2000000000 0x00b400c200000000 0x8f80083800000000 0x58f8008380000000

def z701 : W := mkw 0x1b400c2829601c0a 0x01b400c2829601c0 0xef800e3839c03e0c 0xfef800e3839c03e0

def z702 : W := mkw 0x8f544c2280000000 0x08f544c228000000 0x0e00000000000000 0x00e0000000000000

def z703 : W := mkw 0x26343f02d81ad6b5 0x426343f02d81ad6b 0x2e647600f838c630 0x82e647600f838c63

def z704 : W := mkw 0x4dded04837f7e948 0x84dded04837f7e94 0x7ffff0003ffff9cb 0xf7ffff0003ffff9c

def z705 : W := mkw 0x0000900004144110 0x4000090000414411 0x000000000004c130 0x0000000000004c13

def z706 : W := mkw 0x24140002900280a1 0x024140002900280a 0x6e1c0007f807c1fa 0xe6e1c0007f807c1f

def z707 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe00ffc3ffc3f0f 0xfffe00ffc3ffc3f0

def z708 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3067f604c63ce73a 0x83067f604c63ce73

def z709 : W := mkw 0x0940004823602808 0x0094000482360280 0x7fe001f83ff80009 0xf7fe001f83ff8000

def z710 : W := mkw 0x008b009d00c10848 0x8008b009d00c1084 0xc19b89ff01c739cf 0x7c19b89ff01c739c

def z711 : W := mkw 0xc221bfb7f5b7c000 0x0c221bfb7f5b7c00 0xf0000fffffffc00c 0x0f0000fffffffc00

def z712 : W := mkw 0x82212fb7c0000000 0x082212fb7c000000 0x8063ffffc0000005 0x08063ffffc000000

def z713 : W := mkw 0x1960036823682a0e 0x01960036823682a0 0x7fe007f83ff8260d 0xf7fe007f83ff8260

def z714 : W := mkw 0x008b90dd06d56948 0x8008b90dd06d5694 0xf19b89ff07fff9cf 0x7f19b89ff07fff9c

def z715 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8e7fffffc0000006 0x88e7fffffc000000

def z716 : W := mkw 0xafff6fb7c80014a1 0x0afff6fb7c80014a 0xeffffffff8003fff 0xfeffffffff8003ff

def z717 : W := mkw 0x6bcadc02adb554a1 0x06bcadc02adb554a 0x91e3fe07c7f83ff5 0x191e3fe07c7f83ff

def z718 : W := mkw 0xcdff63b571a38000 0x0cdff63b571a3800 0x4ffbf1f839c30001 0x54ffbf1f839c3000

def z719 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0xb07fffc7c63ce73f 0xeb07fffc7c63ce73

def z720 : W := mkw 0x008a005902c12848 0x8008a005902c1284 0xd19809fb07c318c1 0x5d19809fb07c318c

def z721 : W := mkw 0x84bf6397c0000000 0x084bf6397c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z722 : W := mkw 0x1beb8fb52dad1746 0x81beb8fb52dad174 0x2e7b8607383f07c2 0x82e7b8607383f07c

def z723 : W := mkw 0x269f8cdf9ec7bde9 0x8269f8cdf9ec7bde 0x3f8787f8ffc0c631 0x93f8787f8ffc0c63

def z724 : W := mkw 0x9b606f686b683e0e 0x09b606f686b683e0 0xffe07ff83ff83e0d 0xfffe07ff83ff83e0

def z725 : W := mkw 0x82212fb7c0000000 0x082212fb7c000000 0x8007ffffc0000006 0x08007ffffc000000

def z726 : W := mkw 0x0021b3cc46dd6b5c 0xc0021b3cc46dd6b5 0xf07fffc7c7ffffff 0xef07fffc7c7fffff

def z727 : W := mkw 0x949f60dfeb683e0e 0x0949f60dfeb683e0 0x701ff007fff83e0a 0x0701ff007fff83e0

def z728 : W := mkw 0xef747f22f932d4a1 0x0ef747f22f932d4a 0x2e647600f838c630 0x82e647600f838c63

def z729 : W := mkw 0x3b600f6aab683eaf 0x03b600f6aab683ea 0xffe00ffb3ff83ecd 0xfffe00ffb3ff83ec

def z730 : W := mkw 0x0021b384441c4314 0x40021b384441c431 0x2067f604c03ce73e 0xa2067f604c03ce73

def z731 : W := mkw 0x86bf6fb7c0000000 0x086bf6fb7c000000 0x819fffffc0000007 0x7819fffffc000000

def z732 : W := mkw 0xefde4c33b9a394a1 0x0efde4c33b9a394a 0xcf98083b39c318c0 0x5cf98083b39c318c

def z733 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x21e7f7fcc004e73f 0xb21e7f7fcc004e73

def z734 : W := mkw 0x8fff6fb7d0028000 0x08fff6fb7d002800 0xeffffffff807e73f 0xfeffffffff807e73

def z735 : W := mkw 0x00aa331940d94a5c 0xc00aa331940d94a5 0xe1fc7e3bc1fbdef0 0xde1fc7e3bc1fbdef

def z736 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xaffffffff807c7f7 0xfaffffffff807c7f

def z737 : W := mkw 0x449fd0951497c140 0x8449fd0951497c14 0x001ff0000007c002 0x0001ff0000007c00

def z738 : W := mkw 0x700090483ffffeaf 0x0700090483ffffea 0x700000003ffffff8 0x0700000003ffffff

def z739 : W := mkw 0x56bedf681edffe0e 0x056bedf681edffe0 0x801ffff80007fe06 0x0801ffff80007fe0

def z740 : W := mkw 0x0021b38444144000 0x00021b3844414400 0x3067f7c4c63ce73f 0xa3067f7c4c63ce73

def z741 : W := mkw 0x100090482f7c7e0e 0x0100090482f7c7e0 0x700000003ffcfe08 0x0700000003ffcfe0

def z742 : W := mkw 0x10009048277c6b1e 0x410009048277c6b1 0x3000000007fce738 0x03000000007fce73

def z743 : W := mkw 0x8beb6fb7c0000000 0x08beb6fb7c000000 0x8fe3ffffc0000005 0xf8fe3ffffc000000

def z744 : W := mkw 0x0021b3d5461c6314 0x40021b3d5461c631 0xb067ffffc63ce73f 0xab067ffffc63ce73

def z745 : W := mkw 0x84bf63b7c0000000 0x084bf63b7c000000 0x001ff1ffc0000002 0x0001ff1ffc000000

def z746 : W := mkw 0x0020b340461c6214 0x40020b340461c621 0x3067f7c0c63ce63f 0xa3067f7c0c63ce63

def z747 : W := mkw 0x100090482f7c7f1e 0x4100090482f7c7f1 0x700000003ff83e08 0x0700000003ff83e0

def z748 : W := mkw 0x8fff6fb7d0028000 0x08fff6fb7d002800 0xcffffffff8030007 0xfcffffffff803000

def z749 : W := mkw 0x4dff63c473aba314 0x44dff63c473aba31 0x4f9807c4f9c32734 0x54f9807c4f9c3273

def z750 : W := mkw 0x0b600f6023282204 0x00b600f602328220 0xffe00ff83ff8260d 0xfffe00ff83ff8260

def z751 : W := mkw 0x0021b3cc465c6b1c 0x40021b3cc465c6b1 0xb067fffcc63cff3f 0xab067fffcc63cff3

def z752 : W := mkw 0x008b90dd06d56948 0x8008b90dd06d5694 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z753 : W := mkw 0x0021b3dd46dd6b5c 0xc0021b3dd46dd6b5 0xf067ffffc7ffffff 0xaf067ffffc7fffff

def z754 : W := mkw 0x12009c482f7c7f1e 0x412009c482f7c7f1 0xfe040e04fffcff3e 0xefe040e04fffcff3

def z755 : W := mkw 0xadff63b7d00280a1 0x0adff63b7d00280a 0x01fff1ffc007c1f3 0x101fff1ffc007c1f

def z756 : W := mkw 0x4dded00025b54000 0x04dded00025b5400 0x7ffff0003ff8000b 0xf7ffff0003ff8000

def z757 : W := mkw 0x06bf2f97c0000000 0x006bf2f97c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z758 : W := mkw 0x0021b3d5461c6354 0xc0021b3d5461c635 0x3067f7c7c63ce7ff 0xa3067f7c7c63ce7f

def z759 : W := mkw 0x8f74ef6ac6c52948 0x88f74ef6ac6c5294 0x5e647600c7c739c8 0x85e647600c7c739c

def z760 : W := mkw 0x000190c406146100 0x0000190c40614610 0x3067f7c4c63ce73f 0xa3067f7c4c63ce73

def z761 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xeffffffff800000f 0xfeffffffff800000

def z762 : W := mkw 0x3d74036ab36aaaaf 0x03d74036ab36aaaa 0x11fc01ffc7ffc1f3 0x111fc01ffc7ffc1f

def z763 : W := mkw 0xe49ff097d497c0a1 0x0e49ff097d497c0a 0x001ff007c007c1f2 0x0001ff007c007c1f

def z764 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffff6003fffe60f 0xf7ffff6003fffe60

def z765 : W := mkw 0x9fff6fb7e9281606 0x09fff6fb7e928160 0xeffffffff8383e0f 0xfeffffffff8383e0

def z766 : W := mkw 0x0ffe4f2018029400 0x00ffe4f201802940 0xeffffff83807fe0f 0xfeffffff83807fe0

def z767 : W := mkw 0x0021b3cc465c6b5c 0xc0021b3cc465c6b5 0x3067f7c4c63cffff 0xa3067f7c4c63cfff

def z768 : W := mkw 0x1021b3ec465c6b1e 0x41021b3ec465c6b1 0x3067f7fcc63ce73f 0xa3067f7fcc63ce73

def z769 : W := mkw 0xcdded03135b7c000 0x0cdded03135b7c00 0x7ffff0383fffc00b 0xf7ffff0383fffc00

def z770 : W := mkw 0x49cad00025b54000 0x049cad00025b5400 0x7ffbf0003fff000b 0xf7ffbf0003fff000

def z771 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x01fbf1ff00000003 0x101fbf1ff0000000

def z772 : W := mkw 0xa9eb63b5580294a1 0x0a9eb63b5580294a 0x61e3f1f83807fff9 0x161e3f1f83807fff

def z773 : W := mkw 0x808b609540000000 0x0808b60954000000 0x0183f1f800000001 0x10183f1f80000000

def z774 : W := mkw 0x8dff63b540000000 0x08dff63b54000000 0x8ffff9ff00000007 0xf8ffff9ff0000000

def z775 : W := mkw 0x008b009d00c10848 0x8008b009d00c1084 0xc19b89fb01c318c1 0x5c19b89fb01c318c

def z776 : W := mkw 0x200090481edffffd 0xc200090481edffff 0x700000003ffffff8 0x0700000003ffffff

def z777 : W := mkw 0x500090483fffff1e 0x4500090483fffff1 0x700000003fffff38 0x0700000003fffff3

def z778 : W := mkw 0x00009040061c6314 0x400009040061c631 0x3067f604c63ce73f 0xa3067f604c63ce73

def z779 : W := mkw 0x8fdf4cb780000000 0x08fdf4cb78000000 0x8ffff9ff00000007 0xf8ffff9ff0000000

def z780 : W := mkw 0x1b41bcac6d745d1a 0x41b41bcac6d745d1 0xcf87f83cf9c4d932 0x5cf87f83cf9c4d93

def z781 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19b89fb07c718cb 0x7d19b89fb07c718c

def z782 : W := mkw 0x1b400c682b683e0e 0x01b400c682b683e0 0xff8009f83ff83e0d 0x7ff8009f83ff83e0

def z783 : W := mkw 0xafff6fb7d00280a1 0x0afff6fb7d00280a 0x8fffffffc000c037 0xf8fffffffc000c03

def z784 : W := mkw 0x6dded002b5b7c0a1 0x06dded002b5b7c0a 0x7ffff000ffffc03b 0xf7ffff000ffffc03

def z785 : W := mkw 0x000100dd02402948 0x8000100dd0240294 0xd19809ff07c739cf 0x7d19809ff07c739c

def z786 : W := mkw 0x4414900035b7c000 0x04414900035b7c00 0x7e7ff0003fffc00b 0xe7e7ff0003fffc00

def z787 : W := mkw 0x1b600f682b683f4e 0x81b600f682b683f4 0xffe00ff83ff83fcd 0xfffe00ff83ff83fc

def z788 : W := mkw 0xefff6fb7f9a394a1 0x0efff6fb7f9a394a 0xeffffffff9c7ffff 0xfeffffffff9c7fff

def z789 : W := mkw 0x5000904827fd6a0e 0x05000904827fd6a0 0x1000000007f80000 0x01000000007f8000

def z790 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x0ffff7ffc0000003 0x90ffff7ffc000000

def z791 : W := mkw 0x008b00dd02402808 0x0008b00dd0240280 0xd19b89ff07c739cf 0x7d19b89ff07c739c

def z792 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0x6e1c0607f807fffa 0x86e1c0607f807fff

def z793 : W := mkw 0x194000482b683e0e 0x0194000482b683e0 0xffe009f83ff83e0d 0xfffe009f83ff83e0

def z794 : W := mkw 0x92212ffd4a483e0e 0x092212ffd4a483e0 0x80000ff800003e04 0x080000ff800003e0

def z795 : W := mkw 0x0000904806dd6b5c 0xc0000904806dd6b5 0xf01c0e07c7fffffe 0xef01c0e07c7fffff

def z796 : W := mkw 0xc49ff097d497c110 0x4c49ff097d497c11 0x001ff007c007c132 0x0001ff007c007c13

def z797 : W := mkw 0x8beb6fb7c0000000 0x08beb6fb7c000000 0x81fbffffc0000007 0x781fbffffc000000

def z798 : W := mkw 0x0021b384441c4314 0x40021b384441c431 0x2067f600c038c630 0x82067f600c038c63

def z799 : W := mkw 0x008a805906c52848 0x8008a805906c5284 0xd19b89fb07c738cf 0x7d19b89fb07c738c

def z800 : W := mkw 0x3f743f22f93ad6b7 0x43f743f22f93ad6b 0x2e647600f838c630 0x82e647600f838c63

def z801 : W := mkw 0x9b602f6aeb683e0e 0x09b602f6aeb683e0 0xffe00ff8fff83e0d 0xfffe00ff8fff83e0

def z802 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xeffffffff807d8cf 0xfeffffffff807d8c

def z803 : W := mkw 0xa2212fb7c80014a1 0x0a2212fb7c80014a 0xa067ffffc004ffff 0xaa067ffffc004fff

def z804 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3067f7c0c638e63d 0xa3067f7c0c638e63

def z805 : W := mkw 0x4000904837f7e948 0x84000904837f7e94 0x700000003fffc008 0x0700000003fffc00

def z806 : W := mkw 0x09ca400021200000 0x009ca40002120000 0x7fe3f0003ff80009 0xf7fe3f0003ff8000

def z807 : W := mkw 0x0b612fa448001400 0x00b612fa44800140 0xefe7fffcf804ff3f 0xfefe7fffcf804ff3

def z808 : W := mkw 0x008a001900c10848 0x8008a001900c1084 0xc19809fb01c318c5 0x7c19809fb01c318c

def z809 : W := mkw 0x802123b540000000 0x0802123b54000000 0x0067f7fcc0000007 0xa0067f7fcc000000

def z810 : W := mkw 0x0b612fa440000000 0x00b612fa44000000 0x8fe3fff800000005 0xf8fe3fff80000000

def z811 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffff004ffffc13b 0xf7ffff004ffffc13

def z812 : W := mkw 0x0021b3cc465c6b1c 0x40021b3cc465c6b1 0x7067f7c4c7fcff3f 0xa7067f7c4c7fcff3

def z813 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe40ffcfff83e0f 0xfffe40ffcfff83e0

def z814 : W := mkw 0x12212fec4a483f1e 0x412212fec4a483f1 0x80000ff800003e04 0x080000ff800003e0

def z815 : W := mkw 0xbfff6fb7f92a96a7 0x0bfff6fb7f92a96a 0xeffffffff83fffff 0xfeffffffff83ffff

def z816 : W := mkw 0x002133c442186314 0x4002133c44218631 0x2067f7c4c038e737 0xa2067f7c4c038e73

def z817 : W := mkw 0xafff6fb7c00000a1 0x0afff6fb7c00000a 0x8fffffffc00001f7 0xf8fffffffc00001f

def z818 : W := mkw 0x2f752fa6d80294a1 0x02f752fa6d80294a 0xeffffffff807ffff 0xfeffffffff807fff

def z819 : W := mkw 0x12212fec4a483e0e 0x012212fec4a483e0 0x80000ffcc0003e04 0x080000ffcc0003e0

def z820 : W := mkw 0x8beb6fb540000000 0x08beb6fb54000000 0x0fe3f7f800000001 0x90fe3f7f80000000

def z821 : W := mkw 0x0b600f6823602808 0x00b600f682360280 0xffe00ff83ff8380d 0xfffe00ff83ff8380

def z822 : W := mkw 0x2635bfc6de1ef7b5 0x42635bfc6de1ef7b 0xde7bf9c33e3b18c1 0x4de7bf9c33e3b18c

def z823 : W := mkw 0x8dff63b7c0000000 0x08dff63b7c000000 0x01e7f1f8c0000001 0x101e7f1f8c000000

def z824 : W := mkw 0xc49ff0955497c000 0x0c49ff0955497c00 0x001ff0000007c002 0x0001ff0000007c00

def z825 : W := mkw 0x849f6097c0000000 0x0849f6097c000000 0x801ff9ffc0000006 0x0801ff9ffc000000

def z826 : W := mkw 0x4d5550dd3372e948 0x84d5550dd3372e94 0xae6479ff3838f9c4 0x8ae6479ff3838f9c

def z827 : W := mkw 0x0021238440000000 0x0002123844000000 0x81e7fffcc0000007 0xf81e7fffcc000000

def z828 : W := mkw 0x8fff6fb7d0028000 0x08fff6fb7d002800 0x8fffffffc007c007 0xf8fffffffc007c00

def z829 : W := mkw 0x09ca900025b54000 0x009ca900025b5400 0x7ffff0003fffc00b 0xf7ffff0003fffc00

def z830 : W := mkw 0x0b600f2000000000 0x00b600f200000000 0x8fe7fff800000007 0xf8fe7fff80000000

def z831 : W := mkw 0x049f409500000000 0x0049f40950000000 0x819ff9ff00000007 0x7819ff9ff0000000

def z832 : W := mkw 0xb2212fffca483eaf 0x0b2212fffca483ea 0x80000fffc0003ff4 0x080000fffc0003ff

def z833 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19b89fb07c739c9 0x5d19b89fb07c739c

def z834 : W := mkw 0x408bd0dd06d56948 0x8408bd0dd06d5694 0xd19bf9ff07c739cf 0x7d19bf9ff07c739c

def z835 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x01e3f1fc00000007 0x301e3f1fc0000000

def z836 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe40ff8fff8fe3d 0xfffe40ff8fff8fe3

def z837 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xeffffffff800fe3f 0xfeffffffff800fe3

def z838 : W := mkw 0x808be0dd46c52948 0x8808be0dd46c5294 0xd19bf9ff07c739cf 0x7d19bf9ff07c739c

def z839 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x0fe3f1f800000001 0x10fe3f1f80000000

def z840 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xafffffffc004c00f 0xfafffffffc004c00

def z841 : W := mkw 0xcfff6fb7e1a10000 0x0cfff6fb7e1a1000 0x8fffffffc1c00007 0xf8fffffffc1c0000

def z842 : W := mkw 0x3b600f6aab683eaf 0x03b600f6aab683ea 0xfff80fffffff3fff 0xffff80fffffff3ff

def z843 : W := mkw 0x808b609540000000 0x0808b60954000000 0x819bf9ff00000007 0x7819bf9ff0000000

def z844 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffff600ffffc63b 0xf7ffff600ffffc63

def z845 : W := mkw 0x4d54d00035b7c000 0x04d54d00035b7c00 0x7e67f0003fffc00b 0xa7e67f0003fffc00

def z846 : W := mkw 0x4dde50003132c000 0x04dde50003132c00 0x7ffff0003ff8c00b 0xf7ffff0003ff8c00

def z847 : W := mkw 0x0021b3cc46dd6b5c 0xc0021b3cc46dd6b5 0x3067f7c4c7fce73f 0xa3067f7c4c7fce73

def z848 : W := mkw 0x0414000010028000 0x0041400001002800 0xee1c0e07f807fffe 0xeee1c0e07f807fff

def z849 : W := mkw 0x8fff6fb7c8001400 0x08fff6fb7c800140 0xaffffffff8000607 0xfaffffffff800060

def z850 : W := mkw 0x500090482ffd7e0e 0x0500090482ffd7e0 0x700000003ff83e08 0x0700000003ff83e0

def z851 : W := mkw 0x8021b3f5461c6314 0x48021b3f5461c631 0x3067f7fcc63ce73f 0xa3067f7fcc63ce73

def z852 : W := mkw 0x8beb6fb7c0000000 0x08beb6fb7c000000 0x81e3f9fb00000001 0x181e3f9fb0000000

def z853 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0x7fe007f83ff80609 0xf7fe007f83ff8060

def z854 : W := mkw 0x8fff6fb7c0000110 0x48fff6fb7c000011 0x8fffffffc0000137 0xf8fffffffc000013

def z855 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3067f7c4c63cc733 0x83067f7c4c63cc73

def z856 : W := mkw 0x12000c482b683e0e 0x012000c482b683e0 0xff800ff83ff83e0d 0xfff800ff83ff83e0

def z857 : W := mkw 0x8fff6fb7d0028000 0x08fff6fb7d002800 0xaffffffff800c007 0xfaffffffff800c00

def z858 : W := mkw 0x2ffe4f22980294a1 0x02ffe4f22980294a 0xeffffffff807ffff 0xfeffffffff807fff

def z859 : W := mkw 0x008b209540000000 0x0008b20954000000 0x819ff9ffc0000007 0x7819ff9ffc000000

def z860 : W := mkw 0xafff6fb7d00280a1 0x0afff6fb7d00280a 0xcfffffffc007f9ff 0xfcfffffffc007f9f

def z861 : W := mkw 0x0960032021200000 0x0096003202120000 0x7fe001f83ff80009 0xf7fe001f83ff8000

def z862 : W := mkw 0x9fff6fb7e9201402 0x09fff6fb7e920140 0x8ffffffff8000007 0xf8ffffffff800000

def z863 : W := mkw 0x0dde400000000000 0x00dde40000000000 0x8ffff9f800000007 0xf8ffff9f80000000

def z864 : W := mkw 0x8beb6fb540000000 0x08beb6fb54000000 0x81e3fff800000005 0x181e3fff80000000

def z865 : W := mkw 0x0fff6fa440000000 0x00fff6fa44000000 0x8ffffffcc0000007 0xf8ffffffcc000000

def z866 : W := mkw 0x008bb0dd46d56958 0xc008bb0dd46d5695 0xd19bf9ff07c739cf 0x7d19bf9ff07c739c

def z867 : W := mkw 0x6dded002b5b7c0a1 0x06dded002b5b7c0a 0xfffff807fffff9ff 0xffffff807fffff9f

def z868 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8ffbffffc0000005 0x58ffbffffc000000

def z869 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xcffffffff8033ff7 0xfcffffffff8033ff

def z870 : W := mkw 0x008a804806c52808 0x0008a804806c5280 0xd19b89ff07c739cf 0x7d19b89ff07c739c

def z871 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8fffffffc00701c7 0xf8fffffffc00701c

def z872 : W := mkw 0x008a805906c52948 0x8008a805906c5294 0xd19809fb07c739cd 0x7d19809fb07c739c

def z873 : W := mkw 0x9fff6fb7e1280206 0x09fff6fb7e128020 0x8fffffffc0380007 0xf8fffffffc038000

def z874 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x7067f7c4c63fffff 0xa7067f7c4c63ffff

def z875 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19f89ffc7c7f9ff 0x7d19f89ffc7c7f9f

def z876 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8ffff9fb00000003 0xf8ffff9fb0000000

def z877 : W := mkw 0x0021338440184214 0x4002133844018421 0x2067f7c0c038c631 0x82067f7c0c038c63

def z878 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x1fe3f0003ff80001 0x11fe3f0003ff8000

def z879 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8f9fffffc0000006 0x58f9fffffc000000

def z880 : W := mkw 0x8beb6fb7c0000000 0x08beb6fb7c000000 0x81e7ffffc0000007 0xb81e7ffffc000000

def z881 : W := mkw 0x0021b384441c4314 0x40021b384441c431 0x2067f7c4c03cc737 0xa2067f7c4c03cc73

def z882 : W := mkw 0x0021338440184214 0x4002133844018421 0x2067f604c038c632 0x82067f604c038c63

def z883 : W := mkw 0x0000904806d56948 0x80000904806d5694 0x7000000007fff9c8 0x07000000007fff9c

def z884 : W := mkw 0x8fff6fb540000000 0x08fff6fb54000000 0x8ffffff800000007 0xf8ffffff80000000

def z885 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0x919b89ff07c739c7 0x1919b89ff07c739c

def z886 : W := mkw 0x008b80dd06cd2b5c 0xc008b80dd06cd2b5 0xd19b89ff07c73fff 0x7d19b89ff07c73ff

def z887 : W := mkw 0x09ea432000000000 0x009ea43200000000 0x01e3f1f800000001 0x101e3f1f80000000

def z888 : W := mkw 0x8fff6fb7d8029400 0x08fff6fb7d802940 0xeffffffff807fe0f 0xfeffffffff807fe0

def z889 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x81fbf9fb00000001 0x581fbf9fb0000000

def z890 : W := mkw 0x0ddec00025a50000 0x00ddec00025a5000 0x7ffff0003fff000b 0xf7ffff0003fff000

def z891 : W := mkw 0x802123b540000000 0x0802123b54000000 0x0063f1f800000001 0x00063f1f80000000

def z892 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffbf0003ffb0009 0xf7ffbf0003ffb000

def z893 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe00ff83ffcff3d 0xfffe00ff83ffcff3

def z894 : W := mkw 0x8fdedc73861c6314 0x48fdedc73861c631 0xbf98083b063ce738 0x5bf98083b063ce73

def z895 : W := mkw 0x0ddf409500000000 0x00ddf40950000000 0x0ffff1f800000003 0xf0ffff1f80000000

def z896 : W := mkw 0x8fff6fb7e1200000 0x08fff6fb7e120000 0xcffffffff9c00007 0xfcffffffff9c0000

def z897 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8fffffffc0002737 0xf8fffffffc000273

def z898 : W := mkw 0x0beb2fb540000000 0x00beb2fb54000000 0x8fffffffc0000007 0xf8fffffffc000000

def z899 : W := mkw 0x1b600f682b683f1e 0x41b600f682b683f1 0xffe00ff83ff83f3d 0xfffe00ff83ff83f3

def z900 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x3fe7f0003ffcc00b 0xb3fe7f0003ffcc00

def z901 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe00fff3ff83fcd 0xfffe00fff3ff83fc

def z902 : W := mkw 0x300090483f7effbf 0x4300090483f7effb 0x700000003ffffff8 0x0700000003ffffff

def z903 : W := mkw 0x849f6097c0000000 0x0849f6097c000000 0x019ff1ffc0000003 0x1019ff1ffc000000

def z904 : W := mkw 0x92212fffca483f1e 0x492212fffca483f1 0x80000fffc0003f34 0x080000fffc0003f3

def z905 : W := mkw 0xcdded013b5b7c000 0x0cdded013b5b7c00 0x7ffff0033fffc00b 0xf7ffff0033fffc00

def z906 : W := mkw 0x8fff6fb7c0080214 0x48fff6fb7c008021 0x8fffffffc0000637 0xf8fffffffc000063

def z907 : W := mkw 0x008b009500000000 0x0008b00950000000 0x81fff9ff00000007 0xf81fff9ff0000000

def z908 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8ffffffbc0000001 0xd8ffffffbc000000

def z909 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0x3fe007f83ff8260d 0xb3fe007f83ff8260

def z910 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x81e3f9ff00000005 0x181e3f9ff0000000

def z911 : W := mkw 0x008b90dd06dd6b5c 0xc008b90dd06dd6b5 0xd19b89ff07ff39cf 0x7d19b89ff07ff39c

def z912 : W := mkw 0x0021338440184214 0x4002133844018421 0x2067f7c4c03ce73f 0xa2067f7c4c03ce73

def z913 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x5ffbf0003fff000b 0x75ffbf0003fff000

def z914 : W := mkw 0x2fdf4c97980294a1 0x02fdf4c97980294a 0xeffffffff807ffff 0xfeffffffff807fff

def z915 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x3ffff0003fffc003 0x93ffff0003fffc00

def z916 : W := mkw 0x0fff4fb500000000 0x00fff4fb50000000 0x8fffffff00000007 0xf8fffffff0000000

def z917 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0xfffffe07ffffffff 0xffffffe07fffffff

def z918 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd1fff9ff07c739cf 0xfd1fff9ff07c739c

def z919 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19809ff07c739cc 0x5d19809ff07c739c

def z920 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x0fe3f1f800000001 0xf0fe3f1f80000000

def z921 : W := mkw 0x8fff6fb7c8001400 0x08fff6fb7c800140 0xeffffffff8073fcf 0xfeffffffff8073fc

def z922 : W := mkw 0x008b90dd06dd6b5c 0xc008b90dd06dd6b5 0xf1fff9ff07ffffff 0xff1fff9ff07fffff

def z923 : W := mkw 0x096123a440000000 0x0096123a44000000 0x01e3f1f800000001 0x101e3f1f80000000

def z924 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8ffbfffb00000005 0xf8ffbfffb0000000

def z925 : W := mkw 0x8fff6fb7d0028000 0x08fff6fb7d002800 0xeffffffff807f9cf 0xfeffffffff807f9c

def z926 : W := mkw 0x49cad00025b54000 0x049cad00025b5400 0x5fe3f0003ff80001 0x55fe3f0003ff8000

def z927 : W := mkw 0x0bea4f2000000000 0x00bea4f200000000 0x8fe3fff800000005 0xf8fe3fff80000000

def z928 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19b89ff07c318c7 0x7d19b89ff07c318c

def z929 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xbfe00ff83ff80605 0xfbfe00ff83ff8060

def z930 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8fe7ffffc0000005 0x98fe7ffffc000000

def z931 : W := mkw 0x0021b384441c4214 0x40021b384441c421 0x3067f7c4c63cc63f 0xa3067f7c4c63cc63

def z932 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xff9c0e07ffc7ffff 0xfff9c0e07ffc7fff

def z933 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0x8fffffffc007fff7 0xf8fffffffc007fff

def z934 : W := mkw 0x8ffe4f3380000000 0x08ffe4f338000000 0x8ffffffb00000007 0xf8ffffffb0000000

def z935 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x307ff7c7c63fe7ff 0xa307ff7c7c63fe7f

def z936 : W := mkw 0x0021b3c4469d6354 0xc0021b3c4469d635 0x3067f7c4c63fe7ff 0xa3067f7c4c63fe7f

def z937 : W := mkw 0x100090480e5c7f1e 0x4100090480e5c7f1 0x30000000063cff38 0x030000000063cff3

def z938 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3067f7c4c638e735 0x83067f7c4c638e73

def z939 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3067f7c4c638c637 0xa3067f7c4c638c63

def z940 : W := mkw 0xafff6fb7c80014a1 0x0afff6fb7c80014a 0xafffffffc004ffff 0xfafffffffc004fff

def z941 : W := mkw 0x8fff6fb7f1228000 0x08fff6fb7f122800 0xffffffffffffc00f 0xfffffffffffffc00

def z942 : W := mkw 0x0021b3dd465c6b5c 0xc0021b3dd465c6b5 0xf1e7ffffc7fcffff 0xff1e7ffffc7fcfff

def z943 : W := mkw 0x82ab2fb7c0000000 0x082ab2fb7c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z944 : W := mkw 0x008b90dd06d56948 0x8008b90dd06d5694 0xd1fbf9ff07ff39cf 0x7d1fbf9ff07ff39c

def z945 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x81e3f9f800000005 0x781e3f9f80000000

def z946 : W := mkw 0x4000904827f56948 0x84000904827f5694 0x5000000007ff39c8 0x05000000007ff39c

def z947 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xcfffffffc000380f 0xfcfffffffc000380

def z948 : W := mkw 0x8ffe6f22c0000000 0x08ffe6f22c000000 0x8ffffff8c0000007 0xf8ffffff8c000000

def z949 : W := mkw 0x449fd0951497c000 0x0449fd0951497c00 0x001ff0070007c002 0x0001ff0070007c00

def z950 : W := mkw 0x6dded00035b7c0a1 0x06dded00035b7c0a 0x7ffff0003fffc1fb 0xf7ffff0003fffc1f

def z951 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xcffbf9fb380318c1 0x5cffbf9fb380318c

def z952 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0xb067ffc7c63cffff 0xab067ffc7c63cfff

def z953 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xfff80fff3ff83e0f 0xffff80fff3ff83e0

def z954 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xaffffffff800fff7 0xfaffffffff800fff

def z955 : W := mkw 0x00009048065c6b5c 0xc00009048065c6b5 0x30000000063cfff8 0x030000000063cfff

def z956 : W := mkw 0x26bf2f97d80294a1 0x026bf2f97d80294a 0xeffffffff807ffff 0xfeffffffff807fff

def z957 : W := mkw 0x00ab239540000000 0x000ab23954000000 0xe1ffffffc007ffff 0xfe1ffffffc007fff

def z958 : W := mkw 0x8fff6fb7c0810000 0x08fff6fb7c081000 0xcfffffffc1c30007 0xfcfffffffc1c3000

def z959 : W := mkw 0x0dded00025344000 0x00dded0002534400 0x7ffff0003ffcc00b 0xf7ffff0003ffcc00

def z960 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffff604ffffc00f 0xf7ffff604ffffc00

def z961 : W := mkw 0xafff6fb7c80014a1 0x0afff6fb7c80014a 0x8fffffffc00018c7 0xf8fffffffc00018c

def z962 : W := mkw 0xa49f6097d00280a1 0x0a49f6097d00280a 0xc19ff9ffc007f9ff 0x7c19ff9ffc007f9f

def z963 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x2067f7c4c03ce736 0x82067f7c4c03ce73

def z964 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x01fbf1f800000003 0x701fbf1f80000000

def z965 : W := mkw 0x3f740f22b92a96a7 0x03f740f22b92a96a 0x2e60060038380600 0x82e6006003838060

def z966 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x3ffff0003ff8c003 0xf3ffff0003ff8c00

def z967 : W := mkw 0x0000900004144000 0x0000090000414400 0x3067f600c63cc63b 0xa3067f600c63cc63

def z968 : W := mkw 0x8beb6fb7c0000000 0x08beb6fb7c000000 0x01e3f7f8c0000001 0x101e3f7f8c000000

def z969 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xc19b89ff01c739c6 0x5c19b89ff01c739c

def z970 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xbfffffffc638000f 0xfbfffffffc638000

def z971 : W := mkw 0x0dff639540000000 0x00dff63954000000 0x8fffffffc0000007 0xf8fffffffc000000

def z972 : W := mkw 0x8fdf6cb7c0000000 0x08fdf6cb7c000000 0x8f9ff9ffc0000007 0x78f9ff9ffc000000

def z973 : W := mkw 0x4940900035b7c000 0x04940900035b7c00 0x7fe7f0003fffc00b 0xf7fe7f0003fffc00

def z974 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x01e7f1fcc0000003 0x101e7f1fcc000000

def z975 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19b89ff07c339c5 0x5d19b89ff07c339c

def z976 : W := mkw 0x0021b3dd465c6b5c 0xc0021b3dd465c6b5 0xf07fffffc63fffff 0xef07fffffc63ffff

def z977 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xeffffffff803def7 0xfeffffffff803def

def z978 : W := mkw 0x4dded01135b7c040 0x84dded01135b7c04 0x7ffff0033fffc0cb 0xf7ffff0033fffc0c

def z979 : W := mkw 0x0fdf4c9780000000 0x00fdf4c978000000 0x8fffffffc0000007 0xf8fffffffc000000

def z980 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x81ffffffc0000007 0x181ffffffc000000

def z981 : W := mkw 0x0021b3c4469d6314 0x40021b3c4469d631 0x7067f7c4c7ffe73f 0xa7067f7c4c7ffe73

def z982 : W := mkw 0xbfff6fb7f92a96a7 0x0bfff6fb7f92a96a 0xaffffffff838c637 0xfaffffffff838c63

def z983 : W := mkw 0x4414904837f7e948 0x84414904837f7e94 0xfe1c08073ffff9ce 0xefe1c08073ffff9c

def z984 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xff800ff83ff83e0c 0x5ff800ff83ff83e0

def z985 : W := mkw 0xc9eb63b561a10000 0x0c9eb63b561a1000 0x01e3f1f801c00001 0x101e3f1f801c0000

def z986 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x0ffff7f8c0000003 0xf0ffff7f8c000000

def z987 : W := mkw 0x008bb0dd46d56958 0xc008bb0dd46d5695 0xf19fffffc7c7ffff 0xff19fffffc7c7fff

def z988 : W := mkw 0x0001b08444144110 0x40001b0844414411 0x3067f604c63ce73f 0xa3067f604c63ce73

def z989 : W := mkw 0x0dde400031228000 0x00dde40003122800 0x7ffff0003fffc00b 0xf7ffff0003fffc00

def z990 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xfe7c0e07fe3fffff 0xefe7c0e07fe3ffff

def z991 : W := mkw 0x4000904837f7e808 0x04000904837f7e80 0x700000003ffff808 0x0700000003ffff80

def z992 : W := mkw 0xbfde4c3bb9629cab 0x0bfde4c3bb9629ca 0xcf98083b39c318c0 0x5cf98083b39c318c

def z993 : W := mkw 0x049e90001497c000 0x0049e90001497c00 0x7ffff0003fffc00b 0xf7ffff0003fffc00

def z994 : W := mkw 0x008b00dd02c12948 0x8008b00dd02c1294 0xd19809ff07c339cd 0x7d19809ff07c339c

def z995 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xff9b89ff3fc739cf 0xfff9b89ff3fc739c

def z996 : W := mkw 0xa6bf6fb7d80294a1 0x0a6bf6fb7d80294a 0xee1ffffff807fffe 0xeee1ffffff807fff

def z997 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xdfe009f83ff8380d 0x7dfe009f83ff8380

def z998 : W := mkw 0x00ab239540000000 0x000ab23954000000 0x81fbf9ff00000007 0x781fbf9ff0000000

def z999 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xdfe00ff83ff81805 0xfdfe00ff83ff8180

def z1000 : W := mkw 0x00209340061c6204 0x000209340061c620 0x3067f7c4c63ce73f 0xa3067f7c4c63ce73

def z1001 : W := mkw 0x008b00dd02c12948 0x8008b00dd02c1294 0xc19809fb01c318c0 0x5c19809fb01c318c

def z1002 : W := mkw 0x4000904837ffeb5c 0xc4000904837ffeb5 0x700000003ffffff8 0x0700000003ffffff

def z1003 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x0fe7f7fcc0000007 0xb0fe7f7fcc000000

def z1004 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xf19b8fff07c73fcf 0xff19b8fff07c73fc

def z1005 : W := mkw 0x99eb63b561280206 0x099eb63b56128020 0x01e3f1f800380001 0x101e3f1f80038000

def z1006 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x5ffff0003ffb0003 0xf5ffff0003ffb000

def z1007 : W := mkw 0x12212ffd4a483f5e 0xc12212ffd4a483f5 0x80000fffc0003ff4 0x080000fffc0003ff

def z1008 : W := mkw 0x8b612fb7c0000000 0x08b612fb7c000000 0x8fe7ffffc0000007 0xf8fe7ffffc000000

def z1009 : W := mkw 0x008b90dd06d56948 0x8008b90dd06d5694 0xd19ff9ff07c7f9cf 0x7d19ff9ff07c7f9c

def z1010 : W := mkw 0x0020b340461c6314 0x40020b340461c631 0x3067f600c63ce73b 0xa3067f600c63ce73

def z1011 : W := mkw 0x89eb63b7c0000000 0x089eb63b7c000000 0x01e3f1ffc0000001 0x101e3f1ffc000000

def z1012 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x71e7f7c4c7fce73f 0xf71e7f7c4c7fce73

def z1013 : W := mkw 0x8fff6fb7c0000140 0x88fff6fb7c000014 0x8fffffffc00001c7 0xf8fffffffc00001c

def z1014 : W := mkw 0x4b609f2035b7c000 0x04b609f2035b7c00 0xffe00ff83fffc00d 0xfffe00ff83fffc00

def z1015 : W := mkw 0x1dde40482b683e0e 0x01dde40482b683e0 0x7ffff0003ff83e0b 0xf7ffff0003ff83e0

def z1016 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xaffffffff804e73f 0xfaffffffff804e73

def z1017 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe009f83ff81809 0xfffe009f83ff8180

def z1018 : W := mkw 0x3b600f6aab683eaf 0x03b600f6aab683ea 0xffe40ffffffcffff 0xfffe40ffffffcfff

def z1019 : W := mkw 0x8dff63b540000000 0x08dff63b54000000 0x0ffbf1f800000001 0x50ffbf1f80000000

def z1020 : W := mkw 0x249fb097d497c1f1 0xc249fb097d497c1f 0x001ff007c007c1f2 0x0001ff007c007c1f

def z1021 : W := mkw 0x36149c4abf7effbf 0x436149c4abf7effb 0xfe1c0e07fffffffe 0xefe1c0e07fffffff

def z1022 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x01e3f7fcc0000005 0x101e3f7fcc000000

def z1023 : W := mkw 0x002133c442186214 0x4002133c44218621 0x3067f7c4c638e63f 0xa3067f7c4c638e63

def z1024 : W := mkw 0x008b809504850000 0x0008b80950485000 0xd19b89ff07c739cf 0x7d19b89ff07c739c

def z1025 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xcffffffff807d9f7 0xfcffffffff807d9f

def z1026 : W := mkw 0x0d5490003536c000 0x00d5490003536c00 0x7ffff0003fffc00b 0xf7ffff0003fffc00

def z1027 : W := mkw 0x89eb63b561200000 0x089eb63b56120000 0x7fe3f1f83ff80009 0xf7fe3f1f83ff8000

def z1028 : W := mkw 0x82ab6fb7c0000000 0x082ab6fb7c000000 0x8003ffffc0000004 0x08003ffffc000000

def z1029 : W := mkw 0x19ebb3fd67fd6b5e 0xc19ebb3fd67fd6b5 0x11e3f1f807f80001 0x111e3f1f807f8000

def z1030 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x01e7f1f800000003 0xb01e7f1f80000000

def z1031 : W := mkw 0x8fff6fb7c8001400 0x08fff6fb7c800140 0x8fffffffc0003e07 0xf8fffffffc0003e0

def z1032 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xdfe00ff83ff83e05 0x5dfe00ff83ff83e0

def z1033 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0x7fe007f83ff83e09 0x97fe007f83ff83e0

def z1034 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0x8ffffffff8000007 0xf8ffffffff800000

def z1035 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0xfffff9f83fffc00f 0xffffff9f83fffc00

def z1036 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7e7ff0003fffc00a 0x87e7ff0003fffc00

def z1037 : W := mkw 0x8dff63b7c0000000 0x08dff63b7c000000 0x0ffff1ffc0000003 0xf0ffff1ffc000000

def z1038 : W := mkw 0x4dde400031a38000 0x04dde400031a3800 0x7ffff0003ffb000b 0xf7ffff0003ffb000

def z1039 : W := mkw 0x00009048065c6b1c 0x400009048065c6b1 0x7000000007fcff38 0x07000000007fcff3

def z1040 : W := mkw 0x4dded01135b7c000 0x04dded01135b7c00 0xfffff83b3fffc00b 0xffffff83b3fffc00

def z1041 : W := mkw 0x8dff63b540000000 0x08dff63b54000000 0x0ffff7fcc0000007 0xf0ffff7fcc000000

def z1042 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe00ffcfff83f3d 0xfffe00ffcfff83f3

def z1043 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffff0003fffe73b 0xf7ffff0003fffe73

def z1044 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe00ff83fff3fcd 0xfffe00ff83fff3fc

def z1045 : W := mkw 0x1960036823682a0e 0x01960036823682a0 0xffe009f83ff8380d 0xfffe009f83ff8380

def z1046 : W := mkw 0x1b602f686b683e0e 0x01b602f686b683e0 0xffe47ff8fff83e0d 0xfffe47ff8fff83e0

def z1047 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xeffffffff807c63f 0xfeffffffff807c63

def z1048 : W := mkw 0x86bf6fb7c0000000 0x086bf6fb7c000000 0x8e1fffffc0000006 0xe8e1fffffc000000

def z1049 : W := mkw 0xafff6fb7f92294a1 0x0afff6fb7f92294a 0xffffffffffffffff 0xffffffffffffffff

def z1050 : W := mkw 0x6dded002b5b7c0a1 0x06dded002b5b7c0a 0x7ffff607ffffe7ff 0xf7ffff607ffffe7f

def z1051 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x81ffffffc0000007 0xf81ffffffc000000

def z1052 : W := mkw 0x7f745f22b93ad6a7 0x07f745f22b93ad6a 0x2e647600f838c630 0x82e647600f838c63

def z1053 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe00ff83ff81e01 0xdffe00ff83ff81e0

def z1054 : W := mkw 0x008b809d04c50848 0x8008b809d04c5084 0xd19b89ff07c718cf 0x7d19b89ff07c718c

def z1055 : W := mkw 0xcfff6fb7f1228000 0x0cfff6fb7f122800 0x8ffffffff8000007 0xf8ffffffff800000

def z1056 : W := mkw 0x3b600f682b683eaf 0x03b600f682b683ea 0xffe00ff83ff83ffd 0xfffe00ff83ff83ff

def z1057 : W := mkw 0x002123c442082204 0x0002123c44208220 0x3067f7c4c63ce73f 0xa3067f7c4c63ce73

def z1058 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8fffffffc004c137 0xf8fffffffc004c13

def z1059 : W := mkw 0x9fff6fb7c8081606 0x09fff6fb7c808160 0x8fffffffc0000607 0xf8fffffffc000060

def z1060 : W := mkw 0x0021b3cc465c6b1c 0x40021b3cc465c6b1 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z1061 : W := mkw 0x0940900025344000 0x0094090002534400 0x7fe3f0003ff80009 0xf7fe3f0003ff8000

def z1062 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0xf067ffc4c63cff3f 0xef067ffc4c63cff3

def z1063 : W := mkw 0x8beb6fb540000000 0x08beb6fb54000000 0x8ffbffff00000007 0xf8ffbffff0000000

def z1064 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8fffffffc00039c7 0xf8fffffffc00039c

def z1065 : W := mkw 0x09cb409500000000 0x009cb40950000000 0x81fbf9ff00000007 0x781fbf9ff0000000

def z1066 : W := mkw 0x92212fffca483f4e 0x892212fffca483f4 0x80000fffc0003fc4 0x080000fffc0003fc

def z1067 : W := mkw 0x8dff63b7c0000000 0x08dff63b7c000000 0x81fff9ffc0000007 0x781fff9ffc000000

def z1068 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0xfffff8033fffd8cb 0xffffff8033fffd8c

def z1069 : W := mkw 0x4dded002b5b7c000 0x04dded002b5b7c00 0x7ffff007ffffc00b 0xf7ffff007ffffc00

def z1070 : W := mkw 0x0000904806dd6b5c 0xc0000904806dd6b5 0x5000000007ff39c8 0x05000000007ff39c

def z1071 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19f8fffc7c739cf 0xfd19f8fffc7c739c

def z1072 : W := mkw 0x8fff6fb7c0810040 0x88fff6fb7c081004 0x8fffffffc00300c7 0xf8fffffffc00300c

def z1073 : W := mkw 0x008b90dd06dd6b5c 0xc008b90dd06dd6b5 0xf19f8fffc7ffffff 0xff19f8fffc7fffff

def z1074 : W := mkw 0x00ab239540000000 0x000ab23954000000 0x01e3f1f800000001 0x101e3f1f80000000

def z1075 : W := mkw 0x7fde4c2ab9e39cab 0x07fde4c2ab9e39ca 0xcf98083b39c318c0 0x5cf98083b39c318c

def z1076 : W := mkw 0x0000804806c52948 0x80000804806c5294 0xd19809ff07c739cf 0x7d19809ff07c739c

def z1077 : W := mkw 0x008b00dd02c12848 0x8008b00dd02c1284 0xd19b89ff07c338cf 0x7d19b89ff07c338c

def z1078 : W := mkw 0x4dded00035b7c140 0x84dded00035b7c14 0x7ffff0003fffc1cb 0xf7ffff0003fffc1c

def z1079 : W := mkw 0x8beb6fb548001400 0x08beb6fb54800140 0xefe3fff838003e0d 0xfefe3fff838003e0

def z1080 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19b89ff07c719c3 0x5d19b89ff07c719c

def z1081 : W := mkw 0x66149c4abff7fde9 0x866149c4abff7fde 0xfe1c0e07fffffffe 0xefe1c0e07fffffff

def z1082 : W := mkw 0x0ddf409510028000 0x00ddf40951002800 0xeffff9ff3807f9cf 0xfeffff9ff3807f9c

def z1083 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffff0073fffc1cb 0xf7ffff0073fffc1c

def z1084 : W := mkw 0x8dff63b540000000 0x08dff63b54000000 0x0fe7f1f800000001 0x90fe7f1f80000000

def z1085 : W := mkw 0x0940000021200000 0x0094000002120000 0xffe009f83ff8000d 0xfffe009f83ff8000

def z1086 : W := mkw 0x8fff6fb7e1200000 0x08fff6fb7e120000 0x9fffffffc7f80007 0xf9fffffffc7f8000

def z1087 : W := mkw 0x1b602f686b683e1e 0x41b602f686b683e1 0xffe00ff8fff83e3d 0xfffe00ff8fff83e3

def z1088 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xee180e07f807fffc 0x4ee180e07f807fff

def z1089 : W := mkw 0x49cad00025b54000 0x049cad00025b5400 0x7fe7f0003ffcc00b 0xf7fe7f0003ffcc00

def z1090 : W := mkw 0x500090483fffff4e 0x8500090483fffff4 0x700000003fffffc8 0x0700000003fffffc

def z1091 : W := mkw 0x096123a440000000 0x0096123a44000000 0x01e7f7fcc0000007 0xb01e7f7fcc000000

def z1092 : W := mkw 0x1b400c682b603c0a 0x01b400c682b603c0 0xffe009f83ff8380d 0xfffe009f83ff8380

def z1093 : W := mkw 0x8beb6fb540000000 0x08beb6fb54000000 0x8fe3f9f800000001 0x58fe3f9f80000000

def z1094 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xcffffffff80739cf 0xfcffffffff80739c

def z1095 : W := mkw 0x32212feeca483fbf 0x432212feeca483fb 0x80000fffc0003ff4 0x080000fffc0003ff

def z1096 : W := mkw 0x649fd0979497c1e1 0x8649fd0979497c1e 0x001ff007c007c1f2 0x0001ff007c007c1f

def z1097 : W := mkw 0x02212fa440000000 0x002212fa44000000 0x8067fffcc0000007 0xa8067fffcc000000

def z1098 : W := mkw 0xa6352fb7d80294a1 0x0a6352fb7d80294a 0xee7ffffff807ffff 0xeee7ffffff807fff

def z1099 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0xb1e7fffcc63ce73f 0xfb1e7fffcc63ce73

def z1100 : W := mkw 0x8ddf6097c0000000 0x08ddf6097c000000 0x8ffff9ffc0000007 0xf8ffff9ffc000000

def z1101 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xbfe00ff83ff83e05 0x9bfe00ff83ff83e0

def z1102 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0xfffff8073fffc00f 0xffffff8073fffc00

def z1103 : W := mkw 0x8fff6fb7c8001400 0x08fff6fb7c800140 0xeffffffff804ff3f 0xfeffffffff804ff3

def z1104 : W := mkw 0x0000904806dd6b5c 0xc0000904806dd6b5 0x3000000007fce738 0x03000000007fce73

def z1105 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8fe7fff8c0000005 0xf8fe7fff8c000000

def z1106 : W := mkw 0x00ab239540000000 0x000ab23954000000 0x01e7f7fcc0000007 0xb01e7f7fcc000000

def z1107 : W := mkw 0xc49ff097d497c140 0x8c49ff097d497c14 0x001ff007c007c1c2 0x0001ff007c007c1c

def z1108 : W := mkw 0x0021b3cc46dd6b5c 0xc0021b3cc46dd6b5 0xf1e7fffcc7ffffff 0xff1e7fffcc7fffff

def z1109 : W := mkw 0x449ff0955497c150 0xc449ff0955497c15 0x001ff007c007c1f2 0x0001ff007c007c1f

def z1110 : W := mkw 0x49ebf3dd67fd6b5c 0xc49ebf3dd67fd6b5 0x11e3f1f807f80001 0x111e3f1f807f8000

def z1111 : W := mkw 0xcfff6fb7d0838000 0x0cfff6fb7d083800 0x8fffffffc0030007 0xf8fffffffc003000

def z1112 : W := mkw 0x008b90dd06d56958 0xc008b90dd06d5695 0xd19b89ff07c7f9ff 0x7d19b89ff07c7f9f

def z1113 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffbf0003fffc009 0x57ffbf0003fffc00

def z1114 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffff0003ffff9cb 0xf7ffff0003ffff9c

def z1115 : W := mkw 0x196003682b683e0e 0x0196003682b683e0 0x7fe001f83ff83e09 0xf7fe001f83ff83e0

def z1116 : W := mkw 0x8fff6fb7c8001400 0x08fff6fb7c800140 0xcffffffff8001807 0xfcffffffff800180

def z1117 : W := mkw 0xefff6fb7f9a394a1 0x0efff6fb7f9a394a 0xcffffffff9c318c7 0xfcffffffff9c318c

def z1118 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x1067f7c4c63ce737 0x01067f7c4c63ce73

def z1119 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8fffffffc004210f 0xf8fffffffc004210

def z1120 : W := mkw 0xafff6fb7d00280a1 0x0afff6fb7d00280a 0xafffffffc007e7ff 0xfafffffffc007e7f

def z1121 : W := mkw 0x0940000021200000 0x0094000002120000 0x7fe7f0003ff8000b 0xf7fe7f0003ff8000

def z1122 : W := mkw 0x0b400c482b603c08 0x00b400c482b603c0 0xffe00ff83ff83e0d 0xfffe00ff83ff83e0

def z1123 : W := mkw 0x008b00dd02c12948 0x8008b00dd02c1294 0xc19809ff01c739ce 0x7c19809ff01c739c

def z1124 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe7fff83ff83e0f 0xfffe7fff83ff83e0

def z1125 : W := mkw 0x0021239540000000 0x0002123954000000 0x8067ffffc0000007 0xa8067ffffc000000

def z1126 : W := mkw 0x0020b300441c4214 0x40020b300441c421 0x3067f600c638c631 0x83067f600c638c63

def z1127 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0xfffff8003ffff80f 0xffffff8003ffff80

def z1128 : W := mkw 0x6fde4c02b9a394a1 0x06fde4c02b9a394a 0x4f98000039c30000 0x54f98000039c3000

def z1129 : W := mkw 0x8dff63b540000000 0x08dff63b54000000 0x01fff1f800000003 0x101fff1f80000000

def z1130 : W := mkw 0x4d54d0003536c000 0x04d54d0003536c00 0x7fe7f0003ffcc00b 0xf7fe7f0003ffcc00

def z1131 : W := mkw 0x8fff6fb7e9201400 0x08fff6fb7e920140 0xfffffffffff83e0f 0xffffffffffff83e0

def z1132 : W := mkw 0xa69f6c97d80294a1 0x0a69f6c97d80294a 0xef9ffffff807ffff 0xfef9ffffff807fff

def z1133 : W := mkw 0x09cb409500000000 0x009cb40950000000 0x01e3f1f800000001 0x101e3f1f80000000

def z1134 : W := mkw 0xafff6fb7d00280a1 0x0afff6fb7d00280a 0x8fffffffc00300c7 0xf8fffffffc00300c

def z1135 : W := mkw 0x49cad00025b54000 0x049cad00025b5400 0x3fe3f0003ff80001 0x93fe3f0003ff8000

def z1136 : W := mkw 0x0000904806dd6b5c 0xc0000904806dd6b5 0x1000000007f80000 0x01000000007f8000

def z1137 : W := mkw 0x6fde4c1bb9e39ce9 0x86fde4c1bb9e39ce 0xcf98083b39c318c0 0x5cf98083b39c318c

def z1138 : W := mkw 0x86bf6fb7c0000000 0x086bf6fb7c000000 0x807fffffc0000007 0xa807fffffc000000

def z1139 : W := mkw 0x86352fb7c0000000 0x086352fb7c000000 0x8e7fffffc0000007 0xe8e7fffffc000000

def z1140 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7fe7f0003fffc009 0x97fe7f0003fffc00

def z1141 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffff0043fffe10f 0xf7ffff0043fffe10

def z1142 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xafffffffc000c637 0xfafffffffc000c63

def z1143 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xcfffffffc007000f 0xfcfffffffc007000

def z1144 : W := mkw 0x008bb0dd46d56958 0xc008bb0dd46d5695 0xf1fff9ffc7fff9ff 0xff1fff9ffc7fff9f

def z1145 : W := mkw 0x4000904816d7e948 0x84000904816d7e94 0x5000000007c7f9c8 0x05000000007c7f9c

def z1146 : W := mkw 0x0020b300441c4214 0x40020b300441c421 0x2067f600c03cc632 0x82067f600c03cc63

def z1147 : W := mkw 0x0f752fa6c0000000 0x00f752fa6c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1148 : W := mkw 0x0020330040184214 0x4002033004018421 0x2067f600c038c633 0xa2067f600c038c63

def z1149 : W := mkw 0x008ba0dd46c52948 0x8008ba0dd46c5294 0xd19ff9ffc7c739cf 0x7d19ff9ffc7c739c

def z1150 : W := mkw 0x76149c4abffffeaf 0x076149c4abffffea 0xfe1c0e07fffffffe 0xefe1c0e07fffffff

def z1151 : W := mkw 0x008bb0dd46dd6b5c 0xc008bb0dd46dd6b5 0xf19ff9ffc7ffffff 0x7f19ff9ffc7fffff

def z1152 : W := mkw 0x8dff63b550028000 0x08dff63b55002800 0x6ffff1f83807c00b 0xf6ffff1f83807c00

def z1153 : W := mkw 0x008b809d04c50948 0x8008b809d04c5094 0xc19b89ff01c719c7 0x7c19b89ff01c719c

def z1154 : W := mkw 0x008a005902c12848 0x8008a005902c1284 0xc19809fb01c338c4 0x5c19809fb01c338c

def z1155 : W := mkw 0x0000004802402808 0x0000000480240280 0xd19809fb07c338cd 0x7d19809fb07c338c

def z1156 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xae1c0e07f807fff6 0x8ae1c0e07f807fff

def z1157 : W := mkw 0x9fff6fb7e9281606 0x09fff6fb7e928160 0xfffffffffff8060f 0xffffffffffff8060

def z1158 : W := mkw 0x0000904806d56958 0xc0000904806d5695 0x5000000007c7f9f8 0x05000000007c7f9f

def z1159 : W := mkw 0x1960036823682a0e 0x01960036823682a0 0x5fe001f83ff80001 0x55fe001f83ff8000

def z1160 : W := mkw 0x0dfe432000000000 0x00dfe43200000000 0x0ffff1f800000003 0xf0ffff1f80000000

def z1161 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xf1fb89ff07ff39cf 0xff1fb89ff07ff39c

def z1162 : W := mkw 0xbf746f22f92a96a7 0x0bf746f22f92a96a 0x2e647600f838c630 0x82e647600f838c63

def z1163 : W := mkw 0x22212fdfca483ffd 0xc22212fdfca483ff 0x80000fffc0003ff4 0x080000fffc0003ff

def z1164 : W := mkw 0x8dff63b7c0000000 0x08dff63b7c000000 0x01fbf1fb00000001 0x101fbf1fb0000000

def z1165 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19b8fffc7c73fff 0x7d19b8fffc7c73ff

def z1166 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x7e67f7c4fe3ce73f 0xe7e67f7c4fe3ce73

def z1167 : W := mkw 0x1b600f6823682a0e 0x01b600f6823682a0 0xffe00ff83ff8000d 0xfffe00ff83ff8000

def z1168 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xee7ffe07f807ffff 0xeee7ffe07f807fff

def z1169 : W := mkw 0x008b80dd06cd2b4c 0x8008b80dd06cd2b4 0xf19b89ff07ff3fcf 0x7f19b89ff07ff3fc

def z1170 : W := mkw 0x0021b384441c4314 0x40021b384441c431 0x3067f604c63cc73b 0xa3067f604c63cc73

def z1171 : W := mkw 0x80ab63b540000000 0x080ab63b54000000 0x0003f1f800000000 0x00003f1f80000000

def z1172 : W := mkw 0x8f756fa6c0000000 0x08f756fa6c000000 0x8fe7fffcc0000007 0xf8fe7fffcc000000

def z1173 : W := mkw 0x869f6c97c0000000 0x0869f6c97c000000 0x8f9fffffc0000007 0xf8f9fffffc000000

def z1174 : W := mkw 0x100090482ffd7f5e 0xc100090482ffd7f5 0x700000003ffffff8 0x0700000003ffffff

def z1175 : W := mkw 0x3b600f6aab683eaf 0x03b600f6aab683ea 0xffe00ff8fff83e3d 0xfffe00ff8fff83e3

def z1176 : W := mkw 0xafff6fb7c80014a1 0x0afff6fb7c80014a 0x8fffffffc0000637 0xf8fffffffc000063

def z1177 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe009f83ff83e09 0x5ffe009f83ff83e0

def z1178 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x707ff7c4c63fe73f 0xe707ff7c4c63fe73

def z1179 : W := mkw 0x9beb6fb569281606 0x09beb6fb56928160 0x2fe3f7f838380601 0x92fe3f7f83838060

def z1180 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0xc1fbf9ff000739cf 0x7c1fbf9ff000739c

def z1181 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0xeffffffff8033ecf 0xfeffffffff8033ec

def z1182 : W := mkw 0x008b00dd02c12948 0x8008b00dd02c1294 0xc19b89ff01c339c7 0x7c19b89ff01c339c

def z1183 : W := mkw 0x02200f480a483e0c 0x002200f480a483e0 0xffe00ff83ff83e0d 0xfffe00ff83ff83e0

def z1184 : W := mkw 0x8dff63b7c0000000 0x08dff63b7c000000 0x01fff7ffc0000007 0xb01fff7ffc000000

def z1185 : W := mkw 0xafff6fb7d80294a1 0x0afff6fb7d80294a 0x2fe7f7f8f800c631 0x92fe7f7f8f800c63

def z1186 : W := mkw 0x5000904837ffea0e 0x05000904837ffea0 0x700000003fffc008 0x0700000003fffc00

def z1187 : W := mkw 0x6dded002b5b7c0a1 0x06dded002b5b7c0a 0x7ffff0033fffc0cb 0xf7ffff0033fffc0c

def z1188 : W := mkw 0x4000904827f56948 0x84000904827f5694 0x1000000007f80000 0x01000000007f8000

def z1189 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xf19b89ff07c7ffff 0x7f19b89ff07c7fff

def z1190 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xdfffffffc7c0000f 0xfdfffffffc7c0000

def z1191 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7fe7f0003ff8c009 0xf7fe7f0003ff8c00

def z1192 : W := mkw 0x8fff6fb7e1200000 0x08fff6fb7e120000 0xaffffffff8380007 0xfaffffffff838000

def z1193 : W := mkw 0xa6bf6fb7d80294a1 0x0a6bf6fb7d80294a 0x801fffffc007fff6 0x0801fffffc007fff

def z1194 : W := mkw 0x1b600f6aab683e0e 0x01b600f6aab683e0 0xffe00ffffff83e0d 0xfffe00ffffff83e0

def z1195 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0x1fe001f83ff80001 0x11fe001f83ff8000

def z1196 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x01e7f7f8c0000001 0x901e7f7f8c000000

def z1197 : W := mkw 0x1b600f2029281606 0x01b600f202928160 0xffe00ff83ff8060d 0xfffe00ff83ff8060

def z1198 : W := mkw 0x56149c483ffffe0e 0x056149c483ffffe0 0xfe1c0e003ffffe0e 0xefe1c0e003ffffe0

def z1199 : W := mkw 0x02000c0008001400 0x002000c000800140 0xee1c0e07f807fffe 0xeee1c0e07f807fff

def z1200 : W := mkw 0x49cad00035b7c000 0x049cad00035b7c00 0x7fe3f0003fffc009 0xf7fe3f0003fffc00

def z1201 : W := mkw 0x0b600f2029201400 0x00b600f202920140 0xffe00ff83ff83e0d 0xfffe00ff83ff83e0

def z1202 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x7ffff0003ffbc001 0xd7ffff0003ffbc00

def z1203 : W := mkw 0x8f756fb7c0000000 0x08f756fb7c000000 0x8e67ffffc0000007 0xa8e67ffffc000000

def z1204 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8ffff9ffc0000003 0x58ffff9ffc000000

def z1205 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xffe40ff83ffcfe0f 0xfffe40ff83ffcfe0

def z1206 : W := mkw 0x0020b300441c4214 0x40020b300441c421 0x3067f604c63ce73f 0xa3067f604c63ce73

def z1207 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xefffffffc007ffff 0xfefffffffc007fff

def z1208 : W := mkw 0x0960034823682a0c 0x00960034823682a0 0xffe00ff83ff83e0d 0xfffe00ff83ff83e0

def z1209 : W := mkw 0x26149c4a9edffffd 0xc26149c4a9edffff 0xfe1c0e07fffffffe 0xefe1c0e07fffffff

def z1210 : W := mkw 0x89eb63b540000000 0x089eb63b54000000 0x01e3f7f800000005 0xb01e3f7f80000000

def z1211 : W := mkw 0x600090483ff7fde9 0x8600090483ff7fde 0x700000003ffffff8 0x0700000003ffffff

def z1212 : W := mkw 0xafff6fb7d00280a1 0x0afff6fb7d00280a 0xeffffffff807c1ff 0xfeffffffff807c1f

def z1213 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0x8ffbf9ff00000007 0x78ffbf9ff0000000

def z1214 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xafffffffc000260f 0xfafffffffc000260

def z1215 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xd19b89fb07c338cd 0x7d19b89fb07c338c

def z1216 : W := mkw 0xcfff6fb7f1a38000 0x0cfff6fb7f1a3800 0xfffffffffffb000f 0xffffffffffffb000

def z1217 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xfffc0fffffffffff 0xffffc0ffffffffff

def z1218 : W := mkw 0x89eb63b561200000 0x089eb63b56120000 0x11e3f1f807f80001 0x111e3f1f807f8000

def z1219 : W := mkw 0x8fff6fb7c0000000 0x08fff6fb7c000000 0xcfffffffc00318c7 0xfcfffffffc00318c

def z1220 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xef9c0ffff807ffff 0xfef9c0ffff807fff

def z1221 : W := mkw 0xabeb6fb7c80014a1 0x0abeb6fb7c80014a 0x81e3ffffc0003ff5 0x181e3ffffc0003ff

def z1222 : W := mkw 0x000180cc06442908 0x0000180cc0644290 0xd19b89ff07c739cf 0x7d19b89ff07c739c

def z1223 : W := mkw 0x4dded00035b7c000 0x04dded00035b7c00 0x5ffff0003fffc003 0x55ffff0003fffc00

def z1224 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xfff80ff83fff3e0f 0xffff80ff83fff3e0

def z1225 : W := mkw 0x008b80dd06c52948 0x8008b80dd06c5294 0xf19f89ff07c7f9cf 0xff19f89ff07c7f9c

def z1226 : W := mkw 0xcfff6fb7f1a38000 0x0cfff6fb7f1a3800 0xeffffffff9c7c00f 0xfeffffffff9c7c00

def z1227 : W := mkw 0x26140c02980294a1 0x026140c02980294a 0xce1c0e07f807fff6 0x4ce1c0e07f807fff

def z1228 : W := mkw 0x1960036823682a0e 0x01960036823682a0 0x3fe001f83ff80001 0x93fe001f83ff8000

def z1229 : W := mkw 0x4dded00035b7c110 0x44dded00035b7c11 0x7ffff0003fffc13b 0xf7ffff0003fffc13

def z1230 : W := mkw 0xafff6fb7c80014a1 0x0afff6fb7c80014a 0xcfffffffc0073fff 0xfcfffffffc0073ff

def z1231 : W := mkw 0x8beb6fb540000000 0x08beb6fb54000000 0x8fe7fffcc0000007 0xf8fe7fffcc000000

def z1232 : W := mkw 0x8fff6fb7c0080204 0x08fff6fb7c008020 0xafffffffc0380607 0xfafffffffc038060

def z1233 : W := mkw 0x008ba0dd46c52958 0xc008ba0dd46c5295 0xd19b89ffc7c739ff 0x7d19b89ffc7c739f

def z1234 : W := mkw 0x0ffe4f2280000000 0x00ffe4f228000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1235 : W := mkw 0x0021b3cc465c6b1c 0x40021b3cc465c6b1 0x31e7f7fcc7fce73f 0xb31e7f7fcc7fce73

def z1236 : W := mkw 0x008a005902c12848 0x8008a005902c1284 0xd19809ff07c739cf 0x7d19809ff07c739c

def z1237 : W := mkw 0x008b009d00c10848 0x8008b009d00c1084 0xc19809ff01c318c4 0x5c19809ff01c318c

def z1238 : W := mkw 0x1b600f682b683e0e 0x01b600f682b683e0 0xfff80ffb3ffb3ecd 0xffff80ffb3ffb3ec

def z1239 : W := mkw 0x1b600f2829601c0a 0x01b600f2829601c0 0xffe00ff83ff8180d 0xfffe00ff83ff8180

def z1240 : W := mkw 0x0021b3dd465c6b5c 0xc0021b3dd465c6b5 0x3067f7fcc63ce73f 0xa3067f7fcc63ce73

def z1241 : W := mkw 0x10009048277c6b1e 0x410009048277c6b1 0x1000000007f80000 0x01000000007f8000

def z1242 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3067f7c0c63cc63b 0xa3067f7c0c63cc63

def z1243 : W := mkw 0x0021b3c4461c6314 0x40021b3c4461c631 0x3067f7c0c63ce739 0x83067f7c0c63ce73

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z7,z3,z4,z5]),(0,[z0,z1,z8,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z9,z5]),(0,[z10,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z11,z2,z3,z4,z5])],[(0,[z0,z1,z2,z12,z3,z4,z5]),(0,[z13,z0,z2,z14,z3,z4,z5]),(0,[z0,z1,z15,z2,z3,z4,z16]),(0,[z0,z17,z1,z2,z3,z4,z5])],[(0,[z18,z0,z1,z2,z3,z4,z16]),(0,[z19,z0,z1,z2,z3,z4,z5]),(0,[z20,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z21,z4,z5]),(0,[z0,z1,z22,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z23,z4,z5])],[(0,[z24,z0,z1,z25,z2,z3,z4]),(0,[z0,z26,z1,z2,z3,z4,z5]),(0,[z0,z1,z27,z2,z3,z4,z16])],[(0,[z0,z1,z2,z3,z4,z28,z5]),(0,[z0,z1,z29,z30,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z31,z32]),(0,[z0,z1,z2,z3,z4,z5,z33])],[(0,[z0,z34,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z35,z4,z5]),(0,[z36,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z37,z4,z5]),(1,[z0,z1,z25,z3,z4,z38])],[(0,[z0,z1,z2,z39,z3,z4,z5]),(0,[z0,z1,z2,z3,z40,z4,z5]),(0,[z0,z1,z2,z3,z4,z41,z5]),(0,[z0,z1,z2,z3,z4,z38,z16]),(0,[z0,z1,z2,z3,z4,z16,z42])],[(0,[z0,z43,z1,z2,z3,z4,z5]),(0,[z44,z0,z1,z2,z3,z4,z16])]],
   [[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z24,z1,z45,z2,z3,z4,z5]),(0,[z46,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z47,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z48,z4,z5]),(0,[z0,z1,z2,z3,z4,z49,z5])],[(0,[z0,z1,z2,z50,z3,z4,z5]),(0,[z0,z1,z51,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z52,z4,z5]),(0,[z0,z53,z1,z2,z3,z4,z16]),(0,[z0,z1,z54,z2,z3,z4,z5]),(0,[z0,z1,z2,z55,z3,z4,z5])],[(0,[z0,z1,z2,z56,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z57,z5]),(0,[z58,z0,z1,z59,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z60]),(0,[z0,z1,z2,z3,z4,z61,z5]),(0,[z0,z1,z62,z2,z3,z63,z5])],[(0,[z1,z45,z2,z3,z64,z4,z5]),(0,[z0,z65,z2,z3,z4,z66,z5]),(0,[z0,z1,z67,z2,z3,z4,z5]),(0,[z0,z1,z2,z68,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z69,z5])],[(0,[z0,z1,z2,z3,z4,z70,z5]),(0,[z71,z0,z1,z2,z3,z4,z5])],[(0,[z0,z65,z72,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z64,z4,z16]),(0,[z0,z73,z2,z14,z3,z4,z5])],[(0,[z0,z1,z2,z3,z74,z4,z5]),(0,[z0,z1,z2,z3,z4,z75,z5]),(0,[z0,z1,z2,z3,z76,z4,z5]),(0,[z0,z77,z1,z2,z3,z4,z78]),(0,[z0,z1,z2,z3,z4,z79,z5]),(1,[z80,z1,z2,z3,z4,z5])],[(0,[z81,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z82]),(0,[z0,z1,z2,z3,z4,z16,z83]),(0,[z0,z1,z2,z3,z23,z84,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z85,z5]),(0,[z86,z0,z1,z2,z3,z87,z5]),(0,[z88,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z89,z2,z3,z4,z5]),(1,[z0,z1,z90,z2,z4,z32]),(0,[z91,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z92,z4,z5]),(0,[z0,z1,z2,z3,z93,z4,z5])],[(0,[z0,z1,z2,z3,z4,z94,z5]),(1,[z13,z0,z95,z3,z4,z5]),(0,[z0,z1,z2,z3,z96,z4,z5])],[(0,[z0,z1,z2,z3,z4,z97,z5]),(1,[z0,z1,z29,z3,z41,z5]),(0,[z98,z0,z1,z2,z3,z4,z5])],[(0,[z86,z1,z2,z3,z99,z4,z5]),(0,[z100,z0,z1,z2,z3,z4,z5]),(0,[z58,z0,z72,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z101,z5]),(0,[z0,z1,z2,z3,z4,z5,z102]),(0,[z103,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z104,z3,z4,z5,z83])],[(0,[z105,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z106,z2,z3,z4,z5]),(0,[z107,z108,z0,z1,z2,z3,z4]),(0,[z58,z13,z0,z2,z3,z4,z5]),(1,[z0,z109,z73,z3,z4,z5]),(0,[z0,z110,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z111,z78]),(0,[z0,z1,z2,z3,z4,z112,z16])],[(0,[z0,z1,z2,z113,z3,z114,z5])],[(0,[z0,z1,z115,z2,z3,z4,z5]),(0,[z0,z1,z116,z2,z117,z3,z4]),(0,[z118,z0,z1,z2,z3,z4,z5]),(0,[z108,z0,z1,z2,z3,z4,z119])]],
   [[(0,[z120,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z121,z3,z4,z5]),(0,[z107,z0,z2,z3,z4,z66,z5]),(1,[z0,z1,z2,z3,z4,z122])],[(0,[z0,z1,z2,z3,z63,z99,z5]),(0,[z0,z1,z2,z3,z4,z123,z32]),(0,[z0,z1,z2,z3,z124,z4,z5])],[(0,[z125,z0,z45,z2,z3,z4,z5]),(0,[z86,z126,z1,z2,z3,z4,z5]),(0,[z127,z0,z1,z2,z3,z4,z5]),(0,[z0,z72,z1,z2,z14,z4,z5]),(1,[z125,z0,z2,z3,z128,z5]),(0,[z0,z1,z29,z2,z3,z4,z129]),(0,[z0,z1,z2,z3,z4,z130,z5]),(0,[z0,z1,z2,z3,z131,z4,z5]),(0,[z0,z1,z2,z3,z4,z132,z5]),(0,[z133,z0,z1,z2,z3,z4,z32])],[(0,[z0,z1,z2,z3,z134,z4,z5]),(0,[z135,z0,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z4,z5,z136]),(0,[z0,z1,z29,z3,z4,z41,z5]),(0,[z0,z1,z137,z2,z3,z4,z5]),(0,[z0,z1,z138,z2,z3,z4,z5])],[(0,[z139,z0,z1,z2,z3,z4,z5]),(0,[z126,z0,z1,z2,z3,z4,z32]),(0,[z13,z0,z1,z73,z3,z4,z5]),(0,[z58,z0,z1,z140,z3,z4,z5]),(0,[z0,z1,z2,z113,z3,z4,z16])],[(0,[z18,z65,z1,z2,z3,z4,z5]),(0,[z126,z0,z1,z2,z3,z141,z5]),(0,[z0,z1,z2,z142,z3,z4,z5]),(0,[z143,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z114,z5]),(0,[z0,z1,z2,z3,z4,z5,z144]),(0,[z0,z1,z2,z145,z3,z4,z5]),(0,[z0,z1,z146,z2,z3,z4,z5])],[(0,[z0,z1,z147,z2,z3,z4,z16]),(0,[z86,z0,z1,z2,z148,z4,z5]),(0,[z149,z0,z1,z2,z3,z4,z5]),(0,[z0,z77,z1,z2,z3,z23,z4]),(0,[z0,z1,z62,z2,z3,z150,z5]),(0,[z0,z1,z2,z151,z3,z4,z5]),(0,[z0,z1,z2,z3,z84,z5,z83])],[(0,[z1,z2,z148,z3,z64,z4,z5]),(0,[z58,z152,z1,z2,z3,z4,z5]),(0,[z107,z0,z1,z2,z3,z4,z66]),(0,[z0,z1,z2,z3,z4,z153,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z154,z5]),(0,[z0,z155,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z16,z32])],[(0,[z0,z1,z2,z3,z4,z156,z5]),(0,[z0,z1,z157,z2,z3,z4,z5])],[(0,[z158,z0,z1,z2,z3,z4,z5]),(0,[z86,z1,z2,z3,z64,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z159]),(0,[z0,z1,z2,z160,z3,z4,z5]),(1,[z0,z1,z3,z96,z4,z5]),(0,[z0,z1,z2,z3,z4,z161,z32])],[(0,[z162,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z163,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z164,z5]),(0,[z0,z165,z1,z2,z3,z4,z5]),(0,[z0,z1,z166,z25,z3,z4,z5]),(1,[z0,z1,z104,z3,z4,z5])],[(0,[z0,z1,z2,z167,z3,z4,z5]),(0,[z0,z1,z2,z3,z128,z4,z16]),(0,[z0,z1,z2,z3,z150,z4,z16]),(0,[z0,z1,z2,z3,z168,z4,z5])],[(0,[z0,z65,z73,z2,z3,z4,z5]),(0,[z107,z0,z1,z2,z3,z4,z169]),(0,[z0,z170,z1,z2,z3,z4,z5]),(0,[z0,z1,z171,z2,z3,z4,z83])],[(0,[z0,z1,z2,z3,z4,z5,z172]),(0,[z0,z1,z173,z2,z3,z4,z5])],[(1,[z107,z0,z2,z3,z4,z66]),(0,[z0,z1,z25,z2,z3,z4,z38]),(0,[z174,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z108,z0,z1,z2,z3,z4,z83]),(0,[z0,z2,z3,z175,z176,z4,z5]),(0,[z0,z1,z29,z2,z3,z4,z16]),(0,[z0,z1,z166,z171,z2,z3,z4]),(0,[z0,z1,z177,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z161]),(0,[z0,z1,z2,z3,z4,z178,z5])],[(0,[z0,z1,z2,z3,z179,z4,z5]),(0,[z86,z0,z1,z180,z3,z4,z5]),(0,[z0,z1,z2,z181,z3,z4,z5]),(0,[z182,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z183,z4,z5]),(0,[z0,z184,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z185]),(0,[z0,z1,z2,z3,z186,z4,z5]),(0,[z0,z1,z2,z3,z4,z187,z5]),(0,[z0,z1,z29,z2,z3,z41,z5]),(0,[z0,z1,z166,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z4,z5,z188]),(0,[z0,z1,z2,z3,z4,z5,z189])],[(0,[z13,z0,z45,z2,z3,z4,z5]),(0,[z190,z18,z1,z2,z3,z4,z5]),(0,[z0,z1,z30,z147,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z191,z5]),(0,[z0,z1,z192,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z193]),(0,[z0,z1,z2,z3,z194,z4,z5]),(0,[z0,z1,z62,z2,z3,z4,z32]),(0,[z0,z195,z1,z2,z3,z4,z5])],[(0,[z0,z196,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z197,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z198]),(0,[z0,z1,z30,z95,z3,z4,z5]),(0,[z58,z0,z73,z2,z3,z4,z5]),(0,[z199,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z200]),(0,[z0,z1,z2,z3,z201,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z202]),(0,[z203,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z204,z2,z3,z4,z5]),(0,[z24,z0,z77,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z205,z5]),(0,[z0,z1,z2,z3,z4,z123,z5]),(0,[z206,z0,z1,z2,z3,z4,z5])],[(0,[z18,z1,z2,z117,z3,z4,z5]),(0,[z133,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z207,z2,z3,z4,z5]),(0,[z0,z1,z30,z2,z176,z4,z5])]],
   [[(0,[z126,z0,z1,z29,z2,z3,z5]),(0,[z24,z0,z1,z166,z2,z3,z4]),(0,[z13,z0,z2,z95,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z208]),(0,[z0,z1,z2,z3,z4,z209,z41])],[(0,[z126,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z210,z5]),(0,[z0,z1,z2,z3,z211,z4,z5]),(0,[z0,z1,z212,z2,z3,z4,z5]),(0,[z0,z1,z25,z3,z4,z38,z5])],[(0,[z0,z1,z2,z3,z213,z4,z5]),(0,[z107,z0,z1,z171,z2,z3,z4]),(0,[z0,z1,z2,z3,z214,z4,z5]),(0,[z0,z1,z215,z2,z3,z4,z5]),(0,[z0,z1,z62,z2,z3,z216,z5]),(0,[z0,z1,z2,z217,z3,z4,z5])],[(0,[z218,z0,z1,z2,z148,z4,z5]),(0,[z0,z1,z2,z14,z3,z4,z219]),(0,[z0,z53,z1,z2,z3,z123,z5]),(0,[z0,z77,z1,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z5,z220]),(0,[z0,z1,z2,z3,z221,z4,z5])],[(0,[z0,z1,z2,z3,z222,z4,z5]),(0,[z0,z1,z2,z223,z3,z4,z5])],[(0,[z224,z0,z1,z2,z3,z4,z32]),(0,[z0,z1,z2,z225,z3,z4,z5]),(0,[z0,z109,z73,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z124,z4]),(0,[z0,z1,z2,z3,z4,z16,z5])],[(1,[z190,z1,z147,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z87,z5]),(0,[z108,z0,z226,z2,z3,z4,z5]),(0,[z0,z1,z2,z227,z3,z4,z5]),(0,[z0,z1,z2,z3,z228,z4,z5]),(0,[z0,z1,z2,z3,z229,z4,z5]),(0,[z0,z1,z171,z2,z3,z4,z32])],[(0,[z1,z45,z2,z117,z3,z4,z5]),(0,[z0,z1,z230,z2,z3,z4,z5]),(0,[z231,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z232,z4,z32]),(0,[z0,z1,z2,z3,z4,z32,z83])]],
   [[(0,[z0,z1,z2,z3,z233,z4,z5]),(0,[z18,z1,z2,z3,z99,z4,z5]),(0,[z0,z1,z2,z3,z4,z234,z5]),(0,[z0,z1,z235,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z236,z4,z5]),(0,[z0,z1,z2,z117,z3,z4,z16]),(0,[z135,z0,z1,z2,z3,z99,z5]),(0,[z108,z0,z1,z2,z3,z4,z32]),(0,[z58,z0,z1,z2,z232,z4,z5]),(0,[z125,z0,z53,z2,z3,z4,z5]),(0,[z0,z1,z15,z2,z3,z4,z122]),(0,[z0,z1,z2,z3,z4,z32,z237])],[(0,[z238,z0,z1,z2,z3,z4,z5]),(0,[z190,z239,z1,z2,z3,z4,z5]),(0,[z126,z0,z1,z62,z2,z3,z5]),(0,[z240,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z219]),(0,[z0,z1,z2,z3,z241,z4,z5])],[(0,[z242,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z243,z5]),(0,[z0,z1,z2,z3,z244,z4,z5]),(1,[z10,z1,z2,z3,z4,z5]),(0,[z0,z1,z245,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z246,z4,z5])],[(0,[z0,z1,z2,z3,z4,z247,z5]),(0,[z0,z1,z2,z3,z4,z248,z5]),(0,[z0,z1,z2,z3,z141,z216,z5]),(0,[z0,z73,z2,z95,z3,z4,z5]),(0,[z1,z2,z3,z4,z132,z216,z5]),(0,[z249,z0,z1,z2,z3,z4,z16])],[(0,[z239,z0,z1,z147,z3,z4,z5]),(0,[z0,z1,z250,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z251])],[(0,[z0,z1,z2,z252,z3,z4,z5]),(0,[z0,z1,z73,z3,z176,z4,z5]),(0,[z0,z1,z2,z3,z4,z16,z78])],[(0,[z253,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z254,z5]),(0,[z0,z1,z2,z3,z4,z5,z42])]],
   [[(0,[z1,z45,z2,z3,z99,z4,z5]),(0,[z125,z0,z1,z2,z3,z123,z5]),(0,[z0,z1,z255,z2,z3,z4,z5]),(0,[z0,z1,z62,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z256,z5]),(0,[z0,z1,z2,z3,z4,z5,z257]),(0,[z0,z1,z3,z4,z5,z258,z83])],[(0,[z0,z1,z259,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z99,z4,z16]),(0,[z0,z1,z2,z3,z4,z119,z32]),(1,[z0,z1,z59,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z260,z5])],[(0,[z0,z1,z2,z3,z261,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z262]),(1,[z0,z1,z11,z2,z3,z5]),(0,[z0,z1,z263,z2,z3,z4,z5]),(0,[z0,z1,z90,z2,z3,z4,z32]),(1,[z0,z1,z171,z2,z3,z83])],[(0,[z86,z0,z1,z2,z3,z4,z32]),(0,[z0,z1,z264,z2,z3,z4,z5]),(0,[z0,z1,z2,z140,z3,z4,z5]),(1,[z265,z0,z2,z3,z4,z5]),(0,[z0,z1,z266,z2,z3,z4,z32])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z0,z267,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z268,z3,z4,z5]),(1,[z0,z1,z2,z4,z16,z32])],[(0,[z18,z1,z2,z3,z64,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z269]),(0,[z0,z1,z2,z148,z3,z4,z32]),(1,[z0,z270,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z271,z4,z5]),(0,[z0,z1,z272,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z38,z5,z78]),(0,[z0,z1,z2,z3,z273,z4,z32])],[(0,[z274,z0,z1,z2,z3,z4,z5]),(0,[z86,z0,z1,z275,z3,z4,z5]),(0,[z126,z1,z2,z148,z3,z4,z5]),(0,[z0,z1,z2,z113,z3,z276,z5]),(0,[z0,z1,z277,z2,z3,z4,z5]),(0,[z0,z1,z25,z2,z3,z4,z78]),(0,[z0,z1,z2,z3,z4,z78,z83])]],
   [[(0,[z278,z0,z1,z2,z3,z4,z5]),(0,[z0,z270,z1,z2,z3,z4,z5]),(0,[z0,z77,z1,z2,z3,z4,z5]),(0,[z0,z279,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z41,z16]),(0,[z0,z280,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z32,z32]),(0,[z0,z1,z2,z3,z4,z5,z83])],[(0,[z18,z0,z45,z2,z3,z4,z5]),(0,[z0,z1,z281,z2,z3,z4,z123]),(0,[z282,z0,z1,z2,z3,z4,z5])],[(0,[z224,z0,z1,z2,z3,z4,z5]),(1,[z283,z0,z1,z2,z3,z4]),(1,[z0,z2,z3,z175,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z237]),(0,[z0,z1,z2,z3,z4,z49,z16])],[(0,[z0,z284,z1,z2,z3,z4,z5]),(1,[z126,z1,z2,z3,z141,z5]),(0,[z0,z226,z1,z2,z3,z4,z5]),(0,[z0,z1,z166,z3,z4,z5,z78]),(0,[z0,z1,z2,z55,z3,z4,z16]),(0,[z0,z1,z171,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z285])],[(0,[z86,z0,z1,z2,z3,z183,z5]),(0,[z0,z1,z2,z3,z286,z4,z5]),(0,[z0,z1,z2,z148,z3,z4,z287]),(0,[z0,z1,z2,z3,z232,z4,z5])],[],[(0,[z0,z1,z2,z3,z288,z4,z5]),(0,[z108,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z16,z289]),(1,[z0,z1,z2,z3,z276,z5]),(0,[z0,z1,z29,z166,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z290]),(0,[z0,z291,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z292,z5]),(0,[z108,z0,z51,z2,z3,z4,z5]),(0,[z0,z1,z2,z293,z3,z4,z5]),(0,[z0,z1,z294,z2,z3,z4,z5]),(0,[z80,z0,z1,z2,z3,z4,z5]),(0,[z295,z0,z1,z2,z3,z4,z5]),(0,[z0,z296,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z297,z1,z2,z3,z4,z5]),(0,[z86,z0,z1,z2,z3,z4,z298]),(0,[z0,z1,z2,z3,z276,z4,z5])],[(0,[z135,z1,z2,z3,z99,z4,z5]),(0,[z0,z1,z2,z3,z299,z4,z5]),(0,[z0,z1,z2,z3,z4,z300,z5]),(0,[z0,z1,z301,z2,z3,z4,z5]),(0,[z0,z1,z62,z3,z150,z4,z5])],[(0,[z24,z0,z1,z2,z3,z4,z84]),(0,[z0,z302,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z14,z3,z4,z32]),(0,[z0,z1,z30,z2,z3,z4,z32]),(1,[z0,z1,z166,z3,z4,z78]),(0,[z0,z1,z303,z3,z96,z4,z5]),(0,[z91,z0,z1,z2,z3,z4,z16])],[(0,[z0,z1,z2,z304,z3,z4,z5]),(0,[z0,z1,z305,z2,z3,z4,z5])],[(0,[z1,z2,z148,z3,z99,z4,z5]),(1,[z0,z1,z140,z3,z4,z5]),(0,[z58,z0,z1,z2,z3,z306,z5]),(0,[z0,z1,z171,z62,z2,z3,z5])],[(0,[z190,z0,z1,z147,z3,z4,z5]),(1,[z0,z1,z2,z3,z87,z5]),(0,[z0,z1,z2,z3,z307,z4,z5]),(0,[z0,z1,z2,z3,z308,z4,z5]),(0,[z309,z0,z1,z2,z3,z4,z5]),(0,[z98,z0,z1,z2,z3,z4,z16])],[(0,[z0,z1,z2,z3,z4,z5,z310]),(0,[z0,z1,z2,z3,z4,z141,z32]),(0,[z0,z1,z311,z2,z3,z4,z5]),(0,[z0,z72,z1,z2,z3,z4,z32]),(1,[z0,z1,z3,z271,z4,z5])],[(0,[z0,z1,z312,z2,z3,z4,z5]),(0,[z126,z1,z2,z3,z4,z141,z5]),(0,[z0,z1,z2,z3,z4,z119,z5]),(0,[z313,z0,z1,z2,z3,z4,z5]),(1,[z152,z1,z2,z3,z4,z5]),(0,[z0,z314,z1,z2,z3,z4,z5]),(0,[z0,z1,z25,z2,z3,z23,z4])]],
   [[(0,[z315,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z316,z5]),(0,[z58,z0,z1,z2,z14,z4,z5]),(0,[z0,z1,z2,z3,z306,z4,z5]),(0,[z0,z1,z317,z3,z4,z123,z5]),(0,[z0,z1,z2,z3,z4,z78,z32]),(0,[z0,z1,z90,z2,z3,z4,z5])],[(0,[z86,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z318,z3,z4,z5]),(0,[z218,z0,z1,z2,z3,z4,z32]),(0,[z265,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z266,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z32]),(0,[z0,z1,z2,z3,z4,z16,z319])],[(0,[z1,z2,z3,z99,z4,z141,z5]),(1,[z0,z1,z2,z3,z4,z185]),(0,[z0,z109,z1,z2,z3,z4,z32]),(1,[z0,z1,z2,z3,z4,z188])],[(0,[z0,z1,z2,z148,z3,z4,z5]),(0,[z13,z320,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z321,z5]),(0,[z0,z1,z2,z3,z4,z38,z83]),(0,[z0,z1,z2,z3,z273,z4,z5])],[(0,[z0,z1,z2,z3,z322,z4,z5]),(0,[z0,z1,z2,z323,z3,z4,z5]),(0,[z0,z1,z2,z324,z3,z4,z5]),(0,[z13,z0,z109,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z325,z5]),(0,[z326,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z66,z32]),(0,[z0,z1,z2,z3,z4,z216,z32])],[(0,[z0,z1,z2,z14,z3,z4,z154]),(0,[z0,z1,z2,z327,z3,z4,z5]),(0,[z0,z1,z137,z2,z3,z4,z16])],[],[(0,[z0,z1,z2,z3,z4,z5,z328]),(0,[z86,z0,z329,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z287]),(0,[z0,z330,z1,z2,z3,z4,z5]),(0,[z0,z2,z14,z3,z232,z4,z5]),(0,[z0,z1,z2,z3,z4,z331,z5]),(0,[z0,z1,z2,z3,z4,z5,z332]),(1,[z0,z1,z2,z303,z63,z5]),(0,[z0,z1,z2,z3,z4,z220,z32]),(0,[z0,z1,z2,z3,z4,z333,z5])]],
   [[(0,[z334,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z335]),(0,[z108,z1,z2,z3,z4,z119,z5]),(1,[z0,z1,z2,z3,z4,z336]),(0,[z0,z1,z2,z3,z337,z4,z5])],[(0,[z338,z0,z1,z2,z3,z4,z5]),(0,[z339,z0,z1,z2,z3,z4,z5])],[(0,[z0,z340,z1,z2,z3,z4,z5])],[(0,[z341,z0,z1,z2,z3,z4,z5])],[(0,[z239,z0,z1,z2,z3,z4,z32]),(0,[z1,z147,z2,z117,z3,z4,z5]),(0,[z0,z1,z342,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z343,z5]),(0,[z0,z1,z2,z3,z344,z4,z5])],[(0,[z0,z1,z2,z345,z3,z4,z5]),(0,[z0,z1,z2,z3,z346,z4,z5]),(0,[z0,z1,z59,z2,z3,z4,z5]),(0,[z0,z1,z29,z2,z3,z4,z336]),(0,[z0,z1,z2,z3,z4,z164,z16])],[(0,[z0,z1,z2,z3,z4,z335,z5]),(0,[z0,z1,z2,z3,z4,z32,z347])],[(0,[z0,z1,z2,z3,z348,z4,z5]),(0,[z349,z0,z1,z2,z3,z4,z5]),(0,[z108,z0,z1,z2,z3,z4,z289]),(0,[z13,z0,z1,z95,z3,z4,z5]),(0,[z0,z1,z2,z14,z3,z4,z5]),(0,[z0,z1,z30,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z32,z350]),(0,[z351,z0,z1,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z352,z5])]],
   [[(0,[z0,z1,z2,z353,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z354,z5]),(0,[z0,z1,z2,z3,z4,z5,z355]),(0,[z0,z1,z2,z3,z63,z123,z5]),(0,[z0,z1,z356,z2,z3,z4,z5]),(0,[z0,z1,z357,z2,z3,z4,z5]),(0,[z0,z1,z22,z2,z3,z4,z41])],[(0,[z358,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z359,z3,z4,z5]),(0,[z0,z1,z171,z2,z3,z23,z5])],[(0,[z18,z24,z1,z2,z3,z4,z5]),(1,[z0,z1,z204,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z5,z360]),(0,[z0,z361,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z219]),(0,[z0,z1,z2,z3,z4,z5,z362])],[(0,[z190,z1,z147,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z363,z4,z5]),(0,[z0,z1,z2,z3,z4,z141,z5]),(0,[z0,z72,z1,z2,z3,z4,z5]),(0,[z125,z0,z2,z3,z128,z4,z5])],[(0,[z0,z1,z25,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z38,z32])],[(1,[z239,z1,z117,z3,z4,z5]),(0,[z0,z1,z29,z2,z3,z63,z5])],[(0,[z218,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z180,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z0,z1,z2,z3,z4,z364,z5]),(0,[z0,z1,z365,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z366,z4,z5]),(0,[z0,z109,z1,z2,z3,z4,z5]),(0,[z0,z53,z1,z2,z3,z4,z32]),(0,[z125,z165,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z176,z4,z32]),(0,[z0,z1,z2,z367,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z368])]],
   [[(0,[z0,z1,z369,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z123,z16]),(0,[z0,z1,z2,z3,z370,z4,z5]),(0,[z0,z1,z30,z113,z3,z4,z5]),(0,[z0,z1,z2,z371,z3,z4,z5])],[(0,[z0,z1,z372,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z373,z5]),(0,[z0,z1,z2,z3,z124,z4,z123]),(0,[z0,z1,z374,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z66,z5]),(1,[z0,z1,z15,z176,z4,z5]),(1,[z0,z1,z2,z3,z4,z257]),(0,[z0,z1,z2,z3,z4,z216,z5])],[(0,[z107,z24,z0,z1,z2,z3,z4]),(0,[z0,z1,z15,z3,z176,z4,z5]),(0,[z0,z1,z375,z2,z3,z4,z32])],[(0,[z126,z0,z1,z2,z3,z4,z16]),(0,[z0,z1,z376,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z132,z5]),(0,[z0,z1,z2,z3,z4,z377,z5]),(0,[z378,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z379,z4,z5]),(1,[z0,z1,z62,z3,z150,z5]),(0,[z0,z1,z2,z303,z3,z63,z5]),(0,[z0,z1,z215,z2,z3,z4,z16])],[(1,[z18,z65,z2,z3,z4,z5]),(0,[z380,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z381,z5]),(0,[z382,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z383,z4,z5]),(0,[z0,z1,z2,z3,z4,z84,z38])],[(0,[z0,z1,z2,z3,z384,z4,z5]),(0,[z0,z1,z73,z2,z3,z4,z32]),(0,[z385,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z27,z2,z216,z5]),(0,[z0,z1,z27,z2,z4,z216,z5]),(0,[z0,z1,z2,z3,z4,z386,z5])],[(0,[z0,z109,z1,z95,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z78]),(0,[z0,z1,z2,z3,z4,z5,z347]),(0,[z0,z1,z2,z3,z4,z84,z32]),(0,[z0,z1,z2,z3,z4,z16,z16]),(0,[z0,z1,z2,z387,z3,z4,z5])]],
   [[(0,[z0,z1,z388,z2,z117,z3,z5]),(0,[z0,z1,z2,z3,z4,z5,z350]),(0,[z0,z1,z389,z2,z3,z4,z5]),(0,[z0,z390,z1,z2,z3,z4,z5]),(0,[z0,z1,z30,z3,z150,z4,z5])],[(0,[z239,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z391,z2,z3,z4,z5]),(1,[z218,z1,z2,z148,z4,z5]),(0,[z0,z1,z2,z3,z99,z4,z185]),(0,[z0,z1,z2,z392,z3,z4,z5]),(0,[z393,z0,z1,z2,z3,z4,z5]),(0,[z394,z0,z1,z2,z3,z4,z32]),(0,[z0,z1,z395,z2,z3,z4,z16]),(0,[z0,z1,z396,z2,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z397,z4,z5]),(0,[z0,z1,z73,z2,z3,z4,z136]),(0,[z0,z1,z2,z398,z3,z4,z5]),(0,[z80,z1,z2,z3,z4,z216,z5])],[(0,[z0,z1,z45,z2,z3,z4,z32]),(0,[z190,z0,z1,z2,z3,z4,z32]),(0,[z351,z0,z1,z2,z3,z4,z5]),(0,[z399,z0,z1,z2,z3,z4,z5]),(1,[z165,z1,z2,z3,z4,z5]),(0,[z125,z0,z1,z2,z3,z4,z32])],[(0,[z126,z1,z45,z2,z3,z4,z5]),(0,[z0,z1,z2,z400,z3,z4,z5]),(0,[z0,z401,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z402]),(0,[z0,z1,z27,z2,z3,z4,z188])],[(0,[z0,z1,z403,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z4,z5]),(0,[z0,z1,z2,z3,z99,z4,z335])]],
   [[(0,[z0,z109,z1,z3,z150,z4,z5]),(0,[z404,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z405,z5]),(0,[z0,z1,z2,z3,z4,z406,z5]),(0,[z0,z407,z1,z2,z3,z4,z5])],[(0,[z320,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z95,z3,z4,z32]),(0,[z0,z1,z2,z408,z3,z4,z5]),(0,[z0,z1,z29,z2,z3,z150,z5]),(0,[z0,z1,z25,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z38,z5])],[(0,[z58,z409,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z113,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z410,z5]),(0,[z0,z1,z2,z55,z4,z16,z5])],[(0,[z0,z1,z411,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z412,z5]),(0,[z0,z1,z2,z3,z4,z200,z5]),(0,[z0,z1,z3,z176,z150,z4,z5]),(0,[z413,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z414,z5]),(0,[z415,z0,z1,z2,z3,z4,z5]),(0,[z416,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z176,z4,z5])],[(0,[z0,z1,z417,z2,z3,z4,z5]),(0,[z24,z0,z1,z2,z3,z4,z119]),(0,[z107,z0,z1,z2,z3,z23,z4]),(0,[z418,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z419,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z420,z5])],[(0,[z421,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z422,z2,z3,z4,z5]),(1,[z0,z226,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z423,z5]),(0,[z58,z0,z1,z2,z3,z424,z5]),(0,[z0,z1,z2,z425,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z426])],[(0,[z224,z0,z65,z2,z3,z4,z5]),(0,[z190,z0,z427,z2,z3,z4,z5]),(0,[z428,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z289]),(0,[z0,z1,z2,z3,z4,z5,z429]),(0,[z0,z1,z430,z2,z3,z4,z5]),(0,[z0,z1,z15,z2,z176,z4,z5]),(0,[z0,z1,z375,z2,z3,z4,z5]),(0,[z0,z267,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z23,z4,z16])]],
   [[(0,[z0,z2,z3,z128,z4,z123,z5]),(0,[z0,z1,z2,z3,z4,z431,z5])],[(0,[z432,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z433,z4,z5]),(0,[z0,z1,z434,z2,z3,z4,z5]),(0,[z0,z1,z435,z2,z3,z4,z5]),(0,[z0,z1,z436,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z437,z5]),(1,[z0,z1,z2,z3,z4,z32])],[(0,[z0,z77,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z150,z4,z32])],[(0,[z0,z1,z73,z2,z3,z4,z5]),(0,[z0,z1,z27,z2,z3,z63,z5])],[(0,[z224,z0,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z438,z3,z4,z5]),(1,[z0,z1,z275,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z439]),(1,[z0,z1,z2,z3,z306,z5]),(1,[z0,z77,z2,z3,z4,z169]),(0,[z0,z1,z2,z3,z4,z5,z440]),(0,[z0,z1,z2,z3,z4,z84,z5])],[(0,[z0,z1,z2,z441,z3,z4,z5]),(0,[z0,z65,z1,z2,z3,z4,z32]),(0,[z0,z1,z30,z117,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z442]),(0,[z13,z0,z1,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z5,z443]),(0,[z0,z1,z171,z2,z3,z4,z16])],[(0,[z0,z45,z2,z3,z4,z123,z5]),(1,[z0,z1,z2,z3,z4,z136]),(0,[z0,z1,z2,z3,z232,z4,z16]),(0,[z0,z1,z166,z2,z3,z4,z38]),(0,[z394,z0,z1,z2,z3,z4,z5])],[(0,[z444,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z147,z3,z176,z4,z5]),(1,[z0,z1,z2,z3,z4,z287])]],
   [[(0,[z0,z1,z445,z2,z3,z4,z5]),(0,[z108,z0,z1,z2,z3,z4,z16]),(0,[z13,z0,z1,z29,z3,z4,z5]),(0,[z0,z1,z2,z3,z446,z4,z5]),(0,[z0,z1,z62,z2,z3,z84,z5]),(0,[z0,z1,z166,z2,z3,z4,z32]),(0,[z0,z1,z447,z2,z3,z4,z5])],[(0,[z0,z1,z45,z2,z3,z4,z5]),(0,[z190,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z448,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z183,z5]),(0,[z126,z0,z1,z2,z3,z99,z5]),(0,[z0,z1,z2,z3,z4,z5,z449]),(0,[z125,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z128,z216,z5])],[(0,[z450,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z116,z2,z3,z4,z5]),(0,[z265,z0,z2,z3,z176,z4,z5]),(0,[z0,z1,z171,z25,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z5,z319])],[(0,[z86,z0,z259,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z451,z4,z5]),(0,[z0,z1,z2,z3,z4,z452,z5]),(0,[z0,z1,z453,z2,z3,z4,z5]),(0,[z0,z454,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z455,z3,z4,z5])],[(0,[z456,z0,z1,z2,z3,z4,z5]),(1,[z0,z427,z2,z3,z4,z5]),(0,[z0,z1,z2,z457,z3,z4,z5]),(0,[z0,z1,z2,z3,z458,z4,z5]),(0,[z58,z0,z1,z2,z3,z4,z32]),(0,[z0,z1,z2,z459,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z154]),(0,[z0,z1,z2,z3,z4,z5,z460]),(0,[z0,z1,z461,z2,z3,z4,z5])],[(0,[z462,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z298]),(0,[z0,z1,z463,z2,z3,z4,z5]),(0,[z108,z0,z1,z25,z2,z3,z4]),(0,[z464,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z465,z4,z5]),(0,[z466,z0,z1,z2,z3,z4,z5]),(0,[z467,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z29,z2,z3,z216,z5]),(0,[z0,z1,z2,z3,z4,z84,z78]),(0,[z0,z1,z2,z303,z3,z4,z32]),(1,[z0,z1,z2,z3,z23,z84])],[(0,[z224,z1,z45,z2,z3,z4,z5]),(0,[z86,z0,z1,z2,z3,z4,z355]),(0,[z24,z0,z1,z2,z3,z4,z83]),(0,[z1,z2,z3,z4,z119,z5,z289]),(0,[z0,z1,z2,z95,z3,z4,z5]),(0,[z0,z1,z29,z3,z4,z38,z5]),(0,[z0,z1,z2,z3,z4,z5,z111]),(1,[z0,z1,z2,z3,z4,z254])],[(0,[z0,z1,z2,z468,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z469,z5]),(0,[z470,z0,z1,z2,z3,z4,z5]),(0,[z0,z471,z1,z2,z3,z4,z5]),(0,[z0,z472,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z473,z3,z4,z5]),(0,[z0,z1,z2,z3,z474,z4,z5]),(0,[z0,z1,z475,z2,z3,z4,z5])]],
   [[(1,[z0,z1,z2,z3,z4,z355]),(0,[z107,z0,z1,z2,z3,z4,z38]),(0,[z0,z1,z2,z3,z23,z4,z84])],[(0,[z0,z1,z29,z3,z176,z4,z5]),(0,[z0,z1,z476,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z477,z5]),(0,[z0,z1,z2,z3,z4,z16,z333])],[(1,[z320,z1,z2,z3,z4,z5]),(0,[z107,z0,z1,z2,z3,z4,z32]),(0,[z0,z1,z90,z2,z3,z4,z16])],[(0,[z0,z1,z478,z2,z3,z4,z5]),(0,[z86,z0,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z4,z479,z5])],[(0,[z0,z1,z2,z303,z3,z216,z5])],[(0,[z0,z1,z2,z480,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z481]),(0,[z0,z1,z104,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z482,z4,z5]),(0,[z0,z1,z2,z3,z4,z483,z5]),(0,[z0,z1,z2,z4,z16,z5,z32]),(0,[z0,z1,z171,z2,z3,z4,z84])],[(0,[z0,z484,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z485]),(0,[z239,z0,z1,z117,z3,z4,z5]),(0,[z0,z1,z106,z2,z117,z3,z5]),(1,[z0,z51,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z424,z5]),(0,[z0,z1,z2,z3,z4,z486,z5]),(0,[z0,z1,z487,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z32,z488])]],
   [[(0,[z0,z109,z1,z29,z3,z4,z5]),(0,[z0,z1,z489,z2,z3,z4,z5]),(0,[z0,z1,z30,z2,z113,z4,z5])],[(0,[z0,z1,z2,z3,z490,z4,z5]),(0,[z0,z1,z491,z2,z3,z4,z5]),(0,[z492,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z493]),(0,[z0,z1,z2,z3,z4,z16,z494])],[(0,[z0,z65,z1,z2,z3,z4,z5]),(0,[z13,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z495,z2,z3,z4,z5]),(0,[z0,z1,z2,z113,z3,z4,z496]),(0,[z0,z1,z2,z3,z4,z5,z129])],[(0,[z0,z1,z2,z497,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z169,z32]),(0,[z498,z0,z1,z2,z3,z4,z5])],[(1,[z0,z329,z2,z3,z4,z5]),(1,[z24,z1,z2,z3,z4,z289]),(0,[z0,z1,z499,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z63,z4,z32])],[(0,[z0,z1,z2,z3,z63,z141,z5]),(0,[z0,z500,z1,z2,z3,z4,z5]),(0,[z0,z1,z166,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z501]),(0,[z0,z1,z2,z3,z4,z502,z5]),(0,[z0,z1,z503,z2,z3,z4,z5]),(0,[z0,z1,z2,z504,z3,z4,z5]),(0,[z0,z1,z2,z3,z344,z4,z16])],[(0,[z24,z0,z1,z2,z3,z4,z32]),(1,[z0,z1,z317,z3,z4,z5]),(0,[z0,z1,z2,z3,z3,z4,z32])]],
   [[(0,[z0,z1,z2,z3,z99,z4,z32]),(0,[z0,z1,z2,z3,z4,z505,z5]),(0,[z0,z1,z2,z506,z3,z4,z5])],[(0,[z0,z1,z507,z2,z3,z4,z5]),(0,[z0,z1,z2,z508,z3,z4,z5]),(0,[z0,z1,z2,z3,z509,z4,z5]),(0,[z58,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z14,z3,z4,z16]),(0,[z0,z53,z1,z2,z3,z128,z5]),(0,[z0,z1,z30,z2,z3,z4,z16]),(1,[z0,z1,z2,z3,z4,z496]),(0,[z510,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z511,z2,z3,z4,z5]),(0,[z0,z53,z2,z3,z4,z123,z5]),(0,[z0,z1,z15,z2,z3,z4,z32]),(0,[z0,z1,z2,z303,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z31])],[(0,[z18,z0,z1,z2,z3,z4,z32]),(0,[z0,z1,z388,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z512,z5]),(0,[z86,z0,z1,z2,z64,z4,z5]),(0,[z0,z1,z513,z2,z3,z4,z5]),(0,[z0,z1,z514,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z16,z169]),(0,[z0,z1,z2,z515,z3,z4,z5])],[(0,[z0,z45,z2,z3,z232,z4,z5]),(1,[z0,z1,z516,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z5,z517]),(0,[z0,z1,z2,z3,z4,z518,z5]),(0,[z0,z1,z27,z2,z3,z4,z32])],[(0,[z0,z1,z519,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z141,z16]),(0,[z0,z1,z2,z3,z520,z4,z5]),(0,[z0,z1,z521,z2,z3,z4,z5]),(0,[z0,z1,z522,z2,z3,z4,z5]),(0,[z523,z0,z1,z2,z3,z4,z5]),(0,[z0,z72,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z113,z3,z4,z257]),(0,[z0,z1,z2,z3,z4,z494,z5])],[(0,[z524,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z525,z3,z4,z5]),(0,[z0,z1,z526,z2,z3,z4,z5]),(0,[z0,z1,z281,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z122,z5]),(0,[z0,z1,z527,z2,z3,z4,z5]),(0,[z0,z1,z166,z2,z3,z4,z78])],[(1,[z0,z528,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z99,z216,z5]),(0,[z107,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z488]),(0,[z0,z1,z2,z3,z529,z4,z5]),(0,[z0,z1,z2,z3,z4,z530,z5]),(0,[z531,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z532,z4,z5]),(0,[z44,z0,z1,z2,z3,z4,z32])],[(0,[z0,z1,z29,z171,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z533,z5])],[(0,[z0,z1,z534,z2,z3,z4,z5]),(0,[z0,z1,z2,z535,z3,z4,z5]),(0,[z86,z218,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z536,z3,z4,z5]),(0,[z107,z279,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z496,z5]),(0,[z0,z1,z537,z2,z3,z4,z5]),(0,[z538,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z63,z4,z216,z5])],[(0,[z0,z1,z2,z539,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z540,z5]),(0,[z0,z1,z2,z3,z4,z541,z5]),(0,[z0,z1,z204,z2,z117,z3,z4]),(1,[z0,z1,z116,z2,z3,z4]),(0,[z0,z1,z2,z3,z542,z4,z5]),(0,[z13,z0,z1,z3,z150,z4,z5]),(0,[z0,z1,z543,z2,z3,z4,z5]),(0,[z0,z1,z27,z2,z3,z216,z5]),(0,[z0,z1,z2,z3,z4,z216,z16])],[(0,[z0,z1,z2,z3,z4,z544,z5]),(0,[z0,z1,z2,z3,z175,z4,z5])],[(0,[z545,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z546,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z123,z216,z5])],[(0,[z0,z547,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z64,z4,z32]),(0,[z125,z0,z1,z2,z3,z128,z5]),(1,[z0,z1,z2,z3,z4,z426]),(0,[z0,z1,z166,z3,z150,z4,z5])],[(0,[z190,z0,z1,z117,z3,z4,z5]),(0,[z0,z1,z2,z3,z548,z4,z5]),(0,[z0,z1,z2,z3,z4,z549,z5])]],
   [[(0,[z0,z1,z550,z2,z3,z4,z5]),(1,[z0,z72,z2,z14,z4,z5]),(0,[z0,z77,z1,z2,z3,z4,z66]),(0,[z107,z0,z1,z2,z3,z4,z78]),(1,[z0,z1,z22,z2,z3,z4]),(0,[z0,z1,z551,z2,z3,z4,z32])],[(0,[z0,z1,z2,z3,z4,z298,z5]),(0,[z0,z1,z2,z3,z63,z4,z5]),(0,[z0,z1,z27,z2,z3,z4,z254])],[(0,[z18,z0,z65,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z552,z5]),(0,[z0,z1,z2,z3,z553,z4,z5]),(0,[z0,z1,z2,z554,z3,z4,z5]),(1,[z135,z1,z2,z3,z99,z5]),(0,[z0,z1,z73,z2,z3,z4,z555]),(1,[z409,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z66,z5,z169]),(0,[z0,z1,z2,z3,z4,z5,z258])],[(0,[z239,z0,z1,z2,z3,z4,z16]),(0,[z556,z0,z1,z2,z3,z4,z5]),(0,[z557,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z558,z2,z3,z4,z5]),(0,[z0,z1,z3,z150,z4,z38,z5]),(0,[z0,z1,z487,z303,z3,z4,z5]),(0,[z0,z1,z559,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z560,z5])],[(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z24,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z561,z5]),(0,[z0,z1,z562,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z99,z4,z5]),(1,[z0,z1,z2,z3,z4,z443])],[(1,[z0,z1,z2,z3,z424,z5]),(0,[z0,z77,z1,z2,z3,z4,z169]),(0,[z0,z1,z166,z2,z3,z23,z4]),(0,[z0,z1,z2,z3,z4,z563,z5])],[(0,[z0,z1,z2,z275,z3,z4,z5]),(0,[z0,z1,z2,z3,z564,z4,z5]),(0,[z0,z1,z15,z2,z3,z4,z5])]],
   [[(0,[z18,z0,z1,z2,z3,z4,z5]),(0,[z218,z0,z1,z2,z64,z4,z5]),(0,[z108,z0,z77,z1,z2,z3,z4])],[(0,[z0,z565,z1,z2,z3,z4,z5]),(0,[z566,z0,z1,z2,z3,z4,z5]),(0,[z567,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z209]),(0,[z0,z1,z27,z2,z3,z4,z5])],[(0,[z0,z1,z568,z2,z3,z4,z5]),(0,[z108,z0,z1,z166,z2,z3,z4]),(0,[z569,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z189,z32]),(1,[z0,z1,z2,z55,z4,z16])],[(0,[z283,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z570,z2,z3,z4,z5]),(0,[z0,z1,z571,z2,z3,z4,z5]),(0,[z0,z1,z25,z2,z3,z4,z16])],[(0,[z0,z1,z2,z572,z3,z4,z5]),(0,[z135,z0,z1,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z555,z5]),(0,[z0,z1,z2,z573,z3,z4,z5]),(0,[z0,z1,z2,z574,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z410,z16])],[(0,[z44,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z516,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z575]),(0,[z135,z0,z1,z2,z3,z141,z5]),(0,[z0,z1,z2,z3,z4,z5,z576]),(0,[z0,z1,z2,z3,z577,z4,z5]),(0,[z0,z1,z62,z2,z3,z4,z16]),(0,[z0,z1,z578,z2,z3,z4,z5])],[(0,[z0,z1,z113,z3,z176,z4,z5]),(0,[z0,z1,z2,z3,z176,z4,z16])],[(0,[z579,z0,z1,z2,z3,z4,z5]),(1,[z224,z45,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z580,z5]),(0,[z0,z1,z147,z2,z3,z4,z32]),(0,[z218,z1,z2,z148,z3,z4,z5]),(0,[z0,z53,z1,z2,z3,z4,z5]),(0,[z0,z1,z62,z2,z3,z41,z5])]],
   [[(0,[z0,z65,z2,z3,z4,z123,z5]),(0,[z58,z0,z1,z2,z3,z4,z443]),(0,[z0,z1,z2,z3,z4,z5,z581])],[(0,[z0,z582,z1,z2,z3,z4,z5]),(0,[z0,z1,z583,z2,z3,z4,z5]),(0,[z0,z1,z584,z2,z3,z4,z5])],[(0,[z283,z0,z1,z45,z2,z3,z4]),(0,[z0,z72,z2,z14,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z209,z5]),(0,[z0,z1,z2,z3,z585,z4,z5]),(1,[z0,z1,z3,z4,z5,z258])],[(0,[z126,z18,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z64,z4,z5]),(0,[z0,z1,z2,z586,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z587]),(0,[z0,z77,z1,z171,z2,z3,z4]),(0,[z588,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z589,z5]),(0,[z0,z1,z516,z45,z2,z3,z4]),(0,[z0,z590,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z591,z4,z5]),(1,[z0,z1,z2,z3,z4,z555]),(0,[z0,z1,z73,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z128,z4,z32]),(0,[z0,z1,z551,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z481]),(0,[z0,z170,z1,z2,z3,z4,z32])],[(0,[z125,z0,z65,z2,z3,z4,z5]),(0,[z0,z1,z2,z592,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z289,z32]),(0,[z0,z593,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z594]),(0,[z0,z1,z2,z3,z4,z84,z16]),(0,[z0,z1,z2,z3,z4,z5,z595])],[(0,[z0,z1,z2,z3,z596,z4,z5]),(0,[z0,z1,z2,z597,z3,z4,z5]),(0,[z0,z1,z2,z598,z3,z4,z5]),(0,[z599,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z600,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z601,z3,z4,z5]),(0,[z602,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z603,z2,z3,z4,z5]),(1,[z0,z1,z281,z2,z3,z4]),(0,[z604,z0,z1,z2,z3,z4,z5])],[(0,[z0,z77,z45,z2,z3,z4,z5]),(0,[z0,z45,z2,z3,z4,z66,z5]),(0,[z0,z1,z2,z2,z3,z4,z5]),(1,[z86,z1,z2,z64,z4,z5]),(0,[z0,z1,z605,z2,z3,z4,z5]),(0,[z0,z1,z29,z2,z3,z4,z32]),(0,[z0,z1,z171,z2,z3,z5,z83])],[(0,[z18,z1,z2,z3,z4,z119,z5]),(0,[z606,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z129])],[(0,[z224,z0,z45,z2,z3,z4,z5]),(0,[z0,z1,z45,z2,z3,z4,z16]),(1,[z0,z1,z106,z2,z3,z5]),(0,[z190,z0,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z4,z112,z5]),(0,[z0,z1,z607,z2,z3,z4,z5]),(0,[z0,z1,z608,z2,z3,z4,z5]),(0,[z0,z1,z2,z609,z3,z4,z5]),(0,[z0,z1,z2,z3,z610,z4,z5]),(0,[z125,z0,z1,z2,z3,z4,z16]),(0,[z611,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z612,z4,z5]),(0,[z0,z1,z2,z3,z4,z613,z5]),(0,[z0,z1,z2,z3,z4,z614,z5]),(0,[z0,z1,z2,z3,z615,z4,z5])],[(0,[z0,z1,z2,z3,z616,z4,z5]),(0,[z24,z0,z1,z2,z3,z4,z289]),(0,[z0,z1,z617,z2,z3,z4,z5])],[(0,[z18,z218,z1,z2,z3,z4,z5]),(0,[z0,z1,z528,z2,z3,z4,z5]),(0,[z0,z1,z618,z2,z3,z4,z5])],[(0,[z0,z65,z77,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z619,z5]),(0,[z0,z1,z15,z2,z3,z4,z426]),(0,[z0,z1,z620,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z621,z4,z5]),(0,[z0,z1,z622,z2,z3,z4,z5])]],
   [[(1,[z0,z259,z2,z3,z4,z5]),(0,[z135,z0,z1,z29,z2,z3,z5]),(0,[z0,z1,z2,z95,z3,z4,z16]),(0,[z0,z1,z2,z3,z623,z4,z5])],[(0,[z624,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z625,z2,z3,z4,z5]),(0,[z135,z0,z1,z2,z3,z4,z5]),(0,[z126,z0,z270,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z626,z5]),(0,[z0,z1,z2,z3,z4,z627,z5]),(0,[z0,z1,z2,z303,z3,z4,z481]),(0,[z0,z1,z2,z3,z628,z4,z5]),(0,[z0,z1,z629,z2,z3,z4,z5])],[(0,[z1,z45,z2,z3,z4,z119,z5]),(0,[z0,z1,z2,z3,z4,z630,z5]),(1,[z0,z1,z388,z2,z3,z5]),(0,[z0,z1,z631,z2,z3,z4,z5]),(0,[z0,z1,z2,z113,z3,z4,z5])],[(0,[z0,z1,z117,z3,z176,z4,z5]),(0,[z0,z1,z2,z3,z4,z632,z5]),(0,[z0,z1,z2,z3,z4,z336,z5]),(0,[z0,z1,z633,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z634,z5])],[(0,[z0,z1,z147,z2,z3,z4,z5]),(0,[z635,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z23,z4,z83])],[(0,[z190,z1,z45,z2,z3,z4,z5]),(0,[z636,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z15,z30,z3,z4,z5]),(0,[z0,z1,z637,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z638,z4,z5]),(0,[z639,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z63,z128,z5]),(0,[z0,z1,z29,z62,z3,z4,z5]),(0,[z0,z1,z640,z2,z3,z4,z5])],[(0,[z641,z0,z1,z2,z3,z4,z5]),(0,[z13,z0,z65,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z148,z3,z4,z16]),(0,[z0,z1,z2,z642,z3,z4,z5]),(0,[z0,z1,z2,z3,z643,z4,z5]),(0,[z0,z644,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z16])],[(0,[z0,z329,z1,z2,z3,z4,z5]),(0,[z0,z1,z30,z73,z3,z4,z5]),(1,[z58,z0,z2,z232,z4,z5]),(0,[z0,z77,z2,z3,z4,z5,z169]),(1,[z604,z1,z2,z3,z4,z5]),(0,[z645,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z487,z3,z4,z5])],[(0,[z0,z1,z2,z117,z3,z4,z32]),(0,[z135,z0,z1,z62,z2,z3,z5]),(0,[z0,z1,z2,z3,z128,z4,z5]),(0,[z0,z1,z2,z3,z150,z4,z5])],[(0,[z0,z1,z646,z2,z3,z4,z5]),(0,[z647,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z648,z3,z4,z5]),(0,[z0,z1,z2,z3,z649,z4,z5])],[(0,[z224,z18,z1,z2,z3,z4,z5]),(0,[z0,z65,z1,z2,z3,z4,z16]),(0,[z0,z1,z650,z2,z3,z4,z5]),(0,[z108,z0,z1,z2,z3,z4,z84]),(0,[z13,z0,z1,z2,z3,z4,z16]),(0,[z107,z0,z77,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z169]),(1,[z279,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z651,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z652,z5]),(0,[z0,z65,z2,z3,z232,z4,z5]),(0,[z653,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z654,z4,z5]),(0,[z0,z1,z29,z2,z3,z4,z5])],[(0,[z409,z0,z1,z2,z3,z4,z5]),(0,[z655,z0,z1,z2,z3,z4,z5]),(0,[z656,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z239,z1,z2,z117,z3,z4,z5]),(0,[z0,z1,z657,z2,z3,z4,z5]),(0,[z0,z1,z658,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z16,z66]),(0,[z659,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z343])],[(0,[z0,z660,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z148,z3,z4,z198]),(0,[z0,z109,z1,z73,z3,z4,z5]),(0,[z0,z1,z2,z661,z3,z4,z5]),(0,[z0,z1,z2,z662,z3,z4,z5]),(0,[z0,z1,z663,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z198,z5]),(0,[z0,z1,z2,z303,z63,z4,z5])],[(0,[z0,z45,z73,z2,z3,z4,z5]),(0,[z58,z0,z1,z2,z3,z4,z16]),(0,[z125,z10,z1,z2,z3,z4,z5])],[(0,[z664,z0,z1,z2,z3,z4,z5]),(0,[z65,z1,z45,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z665,z4,z5]),(0,[z0,z1,z2,z303,z3,z4,z16])],[(0,[z190,z0,z660,z2,z3,z4,z5]),(0,[z126,z135,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z666,z4,z5]),(0,[z58,z0,z2,z3,z232,z4,z5]),(0,[z0,z1,z2,z667,z3,z4,z5]),(0,[z0,z668,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z23,z4,z32])],[(0,[z0,z1,z2,z669,z3,z4,z5]),(0,[z0,z77,z1,z2,z3,z4,z38]),(0,[z670,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z671,z4,z5]),(0,[z672,z0,z1,z2,z3,z4,z5]),(0,[z0,z673,z1,z2,z3,z4,z5]),(0,[z0,z1,z674,z2,z3,z4,z5])],[(0,[z0,z1,z675,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z676,z5]),(0,[z677,z0,z1,z2,z3,z4,z5]),(0,[z0,z678,z1,z2,z3,z4,z5])]],
   [[(1,[z471,z1,z2,z3,z4,z5]),(0,[z679,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z95,z3,z176,z4,z5]),(0,[z107,z0,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z4,z41,z32])],[(0,[z680,z0,z1,z2,z3,z4,z5]),(0,[z681,z0,z1,z2,z3,z4,z5]),(0,[z107,z604,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z682,z5]),(0,[z0,z1,z683,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z684,z5]),(0,[z0,z1,z685,z2,z3,z4,z5])],[(0,[z218,z0,z1,z2,z3,z4,z16]),(0,[z0,z1,z29,z2,z3,z84,z5]),(0,[z0,z1,z686,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z687])],[(0,[z0,z72,z45,z2,z3,z4,z5]),(0,[z13,z471,z1,z2,z3,z4,z5]),(0,[z0,z109,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z303,z3,z4,z343]),(0,[z0,z1,z2,z55,z3,z4,z32]),(0,[z0,z1,z395,z2,z3,z4,z5])],[(0,[z0,z1,z180,z2,z3,z4,z5]),(0,[z58,z0,z1,z2,z3,z4,z200]),(1,[z0,z53,z2,z3,z123,z5]),(1,[z0,z1,z30,z113,z4,z5]),(0,[z688,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z90,z2,z4,z5,z32])],[(0,[z0,z1,z2,z3,z689,z4,z5]),(0,[z0,z1,z690,z2,z3,z4,z5])],[(0,[z691,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z117,z3,z4,z5]),(1,[z108,z1,z2,z3,z4,z119]),(0,[z0,z1,z692,z2,z3,z4,z5]),(0,[z0,z1,z3,z271,z4,z123,z5]),(0,[z0,z1,z90,z2,z55,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z693])]],
   [[(0,[z0,z1,z694,z2,z3,z4,z5]),(0,[z108,z24,z1,z2,z3,z4,z5]),(0,[z0,z1,z15,z2,z113,z4,z5]),(0,[z0,z1,z2,z695,z3,z4,z5]),(0,[z0,z1,z11,z2,z3,z5,z78]),(1,[z0,z1,z2,z3,z5,z111])],[],[(0,[z0,z1,z2,z3,z696,z4,z5]),(1,[z0,z660,z2,z3,z4,z5]),(0,[z249,z0,z1,z2,z3,z4,z5]),(0,[z697,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z698,z2,z3,z4,z5]),(0,[z699,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z700,z2,z3,z4,z5]),(0,[z0,z1,z701,z2,z3,z4,z5]),(0,[z0,z72,z1,z2,z232,z4,z5]),(0,[z0,z1,z317,z2,z3,z4,z5]),(0,[z0,z1,z27,z2,z303,z4,z5]),(0,[z0,z1,z2,z3,z63,z4,z16])],[(0,[z0,z1,z2,z3,z4,z702,z5])],[(0,[z218,z1,z45,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z703,z4,z5]),(0,[z0,z1,z2,z3,z4,z704,z5]),(0,[z0,z1,z3,z150,z4,z41,z5])],[(0,[z0,z1,z427,z2,z3,z4,z5]),(0,[z705,z0,z1,z2,z3,z4,z5]),(0,[z24,z1,z2,z3,z4,z5,z289]),(0,[z24,z0,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z4,z16,z119]),(0,[z0,z152,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z114,z5]),(0,[z0,z1,z2,z3,z3,z4,z16])],[(0,[z126,z0,z528,z2,z3,z4,z5]),(0,[z0,z1,z2,z706,z3,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z3,z4,z5]),(0,[z259,z2,z3,z99,z4,z5]),(0,[z0,z1,z2,z142,z4,z32]),(0,[z708,z1,z2,z3,z4,z5]),(0,[z0,z1,z709,z3,z4,z5]),(0,[z0,z1,z11,z2,z3,z84]),(0,[z0,z710,z2,z3,z4,z32]),(0,[z0,z1,z171,z2,z3,z711])],[(0,[z0,z1,z388,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z712]),(0,[z0,z1,z713,z3,z4,z5]),(0,[z0,z714,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z715]),(0,[z152,z73,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z114,z5]),(0,[z0,z1,z2,z3,z4,z716]),(0,[z0,z1,z2,z4,z717,z5]),(0,[z0,z1,z104,z171,z3,z4])],[(0,[z0,z1,z2,z3,z4,z718]),(0,[z0,z1,z631,z2,z4,z32]),(0,[z471,z1,z2,z3,z4,z32]),(0,[z719,z1,z2,z3,z4,z5]),(0,[z0,z720,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z721])],[(0,[z0,z1,z722,z3,z4,z5]),(0,[z0,z1,z2,z723,z4,z5]),(0,[z0,z1,z3,z214,z150,z5]),(0,[z98,z0,z2,z3,z4,z164]),(0,[z0,z1,z3,z4,z16,z724])],[(0,[z0,z1,z2,z3,z4,z725]),(0,[z190,z1,z147,z3,z4,z32]),(0,[z0,z1,z2,z92,z4,z32]),(0,[z0,z1,z2,z3,z276,z257]),(0,[z0,z1,z2,z93,z4,z32]),(0,[z726,z1,z2,z3,z4,z5])],[(0,[z0,z1,z3,z96,z4,z5]),(0,[z0,z1,z2,z3,z84,z129]),(1,[z0,z1,z3,z4,z727]),(0,[z0,z2,z3,z4,z32,z728]),(0,[z0,z1,z104,z171,z3,z5])],[(0,[z0,z1,z2,z3,z4,z16]),(0,[z320,z45,z2,z3,z4,z5]),(0,[z18,z270,z2,z3,z4,z5]),(0,[z0,z1,z3,z729,z4,z5]),(0,[z108,z0,z1,z104,z3,z4]),(0,[z0,z53,z2,z3,z123,z32]),(0,[z0,z1,z30,z113,z4,z32])]],
   [[(0,[z604,z1,z2,z3,z4,z5]),(0,[z0,z51,z2,z3,z4,z16]),(0,[z730,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z731]),(0,[z58,z0,z2,z232,z4,z5]),(0,[z0,z1,z487,z3,z4,z5]),(0,[z1,z2,z3,z4,z32,z732])],[(0,[z0,z1,z2,z223,z4,z32])],[(0,[z0,z1,z2,z3,z4,z733]),(0,[z0,z1,z2,z3,z4,z734]),(0,[z10,z1,z2,z3,z4,z32]),(0,[z279,z1,z2,z3,z4,z16])],[(0,[z735,z45,z2,z3,z4,z5]),(0,[z0,z1,z25,z323,z3,z4]),(0,[z0,z1,z2,z324,z4,z16]),(0,[z0,z1,z657,z176,z4,z5]),(0,[z107,z0,z2,z3,z4,z66])],[(0,[z0,z660,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z736]),(0,[z0,z1,z3,z737,z4,z5]),(0,[z0,z1,z2,z3,z4,z738]),(0,[z0,z1,z3,z739,z41,z5]),(0,[z0,z1,z2,z3,z548,z84]),(0,[z740,z1,z2,z3,z4,z32])],[(0,[z0,z329,z2,z3,z4,z16]),(0,[z0,z1,z741,z2,z3,z4]),(0,[z0,z1,z663,z3,z4,z38]),(0,[z0,z1,z742,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z743]),(0,[z0,z1,z29,z3,z627,z5])],[(0,[z259,z2,z3,z64,z4,z5]),(0,[z744,z1,z2,z3,z4,z5]),(0,[z98,z0,z2,z3,z4,z66]),(0,[z0,z1,z2,z3,z4,z745])],[(0,[z746,z1,z2,z3,z4,z5]),(0,[z0,z1,z166,z11,z3,z4]),(0,[z0,z1,z2,z3,z4,z343])]],
   [[(0,[z190,z427,z147,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z198]),(0,[z0,z1,z747,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z748]),(0,[z0,z1,z104,z3,z4,z78])],[(0,[z0,z1,z2,z3,z749,z5]),(0,[z0,z1,z750,z3,z4,z5]),(0,[z751,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z200]),(0,[z0,z1,z59,z3,z4,z32]),(0,[z0,z1,z3,z4,z5,z727]),(0,[z80,z752,z2,z3,z4,z5]),(0,[z753,z1,z2,z3,z4,z5])],[(0,[z0,z1,z754,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z755])],[(0,[z86,z1,z2,z654,z4,z5]),(0,[z0,z1,z2,z3,z756,z5])],[(0,[z0,z45,z317,z3,z4,z5]),(0,[z0,z1,z757,z2,z3,z4]),(0,[z758,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z66,z759])],[(0,[z283,z24,z1,z2,z3,z4]),(0,[z0,z710,z2,z3,z4,z5]),(0,[z760,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z761]),(1,[z0,z1,z762,z4,z5]),(0,[z0,z1,z3,z4,z5,z763])],[(0,[z0,z1,z2,z3,z764,z5]),(0,[z0,z1,z2,z3,z4,z765]),(0,[z0,z1,z766,z2,z3,z4]),(0,[z0,z1,z27,z2,z216,z188])],[(0,[z471,z1,z2,z3,z4,z5]),(0,[z767,z1,z2,z3,z4,z5]),(0,[z1,z768,z2,z3,z4,z5]),(0,[z0,z1,z622,z3,z4,z38]),(0,[z0,z2,z3,z4,z5,z728]),(0,[z0,z1,z2,z3,z16,z769])]],
   [[(0,[z0,z1,z2,z3,z770,z5]),(0,[z0,z1,z2,z3,z4,z771]),(0,[z0,z1,z2,z4,z772,z32])],[(0,[z45,z2,z3,z236,z4,z5]),(0,[z0,z1,z2,z3,z4,z773]),(0,[z0,z1,z2,z3,z4,z774]),(0,[z0,z2,z3,z175,z4,z32]),(0,[z1,z2,z3,z4,z5,z732])],[(0,[z190,z1,z147,z3,z4,z5]),(0,[z0,z1,z204,z106,z2,z3]),(0,[z126,z1,z2,z3,z141,z32]),(0,[z0,z1,z266,z3,z4,z237]),(0,[z249,z1,z2,z3,z4,z333]),(0,[z0,z775,z2,z3,z4,z16])],[(0,[z0,z1,z2,z776,z3,z4]),(0,[z0,z1,z388,z116,z2,z3]),(0,[z0,z1,z2,z3,z4,z777]),(0,[z0,z1,z2,z651,z4,z16]),(0,[z0,z1,z3,z4,z38,z102]),(0,[z778,z1,z2,z3,z4,z16])],[(0,[z0,z1,z2,z3,z4,z779]),(0,[z1,z780,z117,z3,z4,z5]),(0,[z239,z1,z106,z117,z3,z5]),(0,[z0,z781,z2,z3,z4,z5]),(0,[z0,z53,z2,z3,z123,z5]),(0,[z0,z1,z30,z113,z4,z5])],[(0,[z0,z1,z782,z3,z4,z5]),(0,[z13,z471,z95,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z783]),(0,[z0,z1,z2,z3,z276,z32])],[(0,[z108,z1,z2,z3,z4,z119]),(0,[z0,z1,z2,z3,z784,z5])],[(0,[z10,z1,z2,z3,z4,z5]),(0,[z108,z51,z2,z3,z4,z119]),(0,[z785,z0,z2,z3,z4,z5]),(0,[z0,z1,z166,z3,z4,z727]),(0,[z0,z1,z2,z3,z786,z16])]],
   [[(0,[z0,z1,z787,z3,z4,z5]),(0,[z80,z1,z2,z3,z4,z32]),(0,[z0,z1,z104,z3,z23,z4])],[(0,[z0,z660,z2,z3,z4,z5]),(0,[z283,z1,z2,z3,z4,z119]),(0,[z18,z1,z2,z3,z4,z335]),(0,[z80,z1,z2,z3,z141,z5]),(0,[z0,z1,z389,z2,z216,z5]),(0,[z0,z1,z2,z3,z4,z788]),(0,[z0,z1,z29,z3,z209,z41]),(0,[z0,z1,z2,z3,z4,z789]),(0,[z740,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z790]),(1,[z0,z722,z3,z4,z5]),(1,[z0,z2,z723,z4,z5]),(0,[z0,z1,z317,z3,z124,z4]),(0,[z0,z791,z2,z3,z4,z32]),(0,[z91,z1,z2,z3,z4,z112])],[(0,[z239,z1,z388,z117,z3,z5]),(0,[z135,z1,z2,z3,z99,z16]),(0,[z0,z1,z2,z792,z4,z5]),(0,[z0,z1,z140,z3,z4,z32]),(0,[z0,z1,z793,z3,z4,z5]),(0,[z0,z77,z2,z3,z4,z759]),(0,[z0,z1,z2,z3,z16,z794])],[(0,[z795,z0,z1,z2,z3,z4]),(0,[z0,z1,z3,z4,z5,z796]),(0,[z0,z1,z2,z3,z4,z797]),(0,[z798,z1,z2,z3,z4,z5])],[(0,[z18,z735,z2,z3,z4,z5]),(0,[z0,z799,z2,z3,z4,z5]),(0,[z0,z1,z3,z271,z4,z32])],[(0,[z309,z45,z2,z3,z4,z5]),(0,[z0,z2,z3,z800,z4,z5]),(0,[z0,z1,z59,z3,z4,z5]),(0,[z152,z1,z2,z3,z4,z32]),(0,[z0,z1,z140,z3,z306,z5]),(0,[z0,z1,z3,z4,z5,z801]),(0,[z0,z1,z171,z2,z3,z530])],[(0,[z0,z1,z2,z3,z4,z802]),(0,[z0,z1,z2,z3,z4,z803]),(0,[z58,z0,z2,z232,z4,z443])]],
   [[(0,[z804,z1,z2,z3,z4,z5]),(0,[z0,z109,z73,z3,z4,z555]),(0,[z0,z1,z2,z3,z805,z4]),(0,[z0,z1,z806,z2,z3,z16])],[(0,[z0,z1,z807,z2,z3,z4]),(0,[z152,z1,z2,z3,z306,z5]),(0,[z0,z808,z2,z3,z4,z5]),(0,[z1,z27,z2,z132,z216,z5]),(0,[z1,z2,z3,z4,z132,z809]),(0,[z0,z1,z2,z4,z16,z32])],[(0,[z0,z1,z810,z2,z3,z4]),(0,[z0,z1,z137,z2,z3,z319])],[(0,[z224,z735,z2,z3,z4,z5]),(0,[z18,z1,z204,z2,z3,z4]),(0,[z0,z1,z2,z3,z811,z5]),(0,[z107,z0,z51,z2,z3,z4]),(0,[z812,z1,z2,z3,z4,z5])],[(0,[z0,z1,z813,z3,z4,z5]),(0,[z0,z1,z814,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z815]),(0,[z816,z1,z2,z3,z4,z5]),(0,[z125,z0,z2,z3,z128,z32]),(0,[z0,z1,z2,z3,z4,z817])],[(0,[z0,z1,z2,z3,z818,z4]),(0,[z0,z1,z819,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z820]),(0,[z409,z1,z2,z3,z4,z200]),(0,[z0,z1,z821,z3,z4,z5]),(0,[z0,z1,z215,z3,z4,z42])],[(0,[z283,z0,z1,z2,z3,z4]),(0,[z218,z1,z2,z572,z4,z5]),(0,[z1,z2,z822,z64,z4,z5]),(0,[z0,z1,z2,z3,z4,z823]),(0,[z0,z2,z3,z175,z4,z5]),(0,[z265,z798,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z824])],[(0,[z126,z1,z2,z3,z141,z5]),(0,[z0,z1,z2,z244,z4,z32]),(0,[z107,z0,z2,z3,z615,z4])]],
   [[(0,[z224,z45,z2,z3,z4,z16]),(0,[z13,z0,z441,z3,z4,z5]),(0,[z265,z0,z95,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z825]),(0,[z0,z2,z3,z128,z826,z5])],[(0,[z120,z45,z2,z3,z4,z5]),(0,[z827,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z424,z200]),(0,[z279,z2,z3,z4,z66,z5]),(0,[z0,z1,z2,z3,z4,z828])],[(0,[z0,z1,z829,z2,z3,z5]),(0,[z86,z259,z2,z64,z4,z5]),(0,[z0,z1,z830,z2,z3,z4]),(0,[z0,z1,z2,z3,z276,z5]),(0,[z0,z1,z831,z2,z3,z4]),(0,[z0,z1,z2,z3,z32,z832])],[(0,[z0,z833,z2,z3,z4,z5]),(0,[z0,z2,z3,z834,z4,z5])],[(0,[z80,z1,z29,z2,z3,z5])],[(0,[z0,z1,z2,z3,z4,z835]),(0,[z0,z1,z836,z3,z4,z5]),(0,[z80,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z837]),(0,[z0,z1,z3,z96,z4,z481]),(0,[z0,z1,z2,z303,z717,z5]),(0,[z0,z1,z104,z3,z4,z32]),(0,[z0,z2,z3,z4,z838,z16]),(0,[z0,z1,z2,z3,z4,z711])],[(0,[z0,z1,z2,z3,z4,z839]),(0,[z0,z1,z2,z3,z4,z840]),(0,[z0,z1,z2,z3,z4,z841]),(0,[z0,z1,z3,z842,z4,z5]),(0,[z0,z2,z3,z175,z4,z843]),(1,[z0,z1,z3,z739,z5]),(0,[z0,z1,z166,z3,z4,z78])],[(0,[z0,z1,z2,z3,z844,z5]),(0,[z0,z1,z2,z3,z845,z5]),(0,[z1,z2,z3,z749,z141,z5]),(0,[z0,z1,z2,z3,z846,z5]),(0,[z0,z791,z2,z3,z4,z5]),(0,[z0,z1,z2,z665,z4,z16]),(0,[z0,z1,z487,z3,z4,z481]),(0,[z0,z1,z90,z2,z4,z32]),(0,[z847,z1,z2,z3,z4,z32])]],
   [[(0,[z0,z77,z2,z3,z4,z517]),(0,[z13,z0,z95,z3,z4,z16])],[(0,[z0,z1,z848,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z1,z2,z3,z4,z850]),(0,[z1,z2,z3,z4,z851,z16])],[(0,[z0,z1,z388,z30,z3,z5]),(0,[z86,z1,z2,z64,z4,z16]),(0,[z0,z1,z2,z3,z4,z852]),(0,[z0,z1,z3,z271,z4,z5]),(0,[z0,z1,z853,z3,z4,z5])],[(0,[z152,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z854]),(0,[z855,z1,z2,z3,z4,z5]),(0,[z0,z109,z73,z3,z4,z16]),(0,[z0,z1,z856,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z857]),(0,[z0,z1,z2,z3,z858,z4]),(0,[z0,z1,z2,z63,z717,z5])],[(0,[z0,z1,z106,z2,z3,z16]),(0,[z0,z859,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z860]),(0,[z0,z1,z861,z3,z4,z5])],[(0,[z0,z45,z281,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z862]),(0,[z0,z1,z863,z2,z3,z4]),(0,[z0,z1,z3,z4,z5,z724]),(0,[z0,z1,z29,z22,z3,z5]),(0,[z0,z1,z2,z3,z4,z864])],[(0,[z0,z1,z865,z2,z3,z4]),(0,[z0,z866,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z185]),(0,[z0,z1,z2,z4,z16,z193]),(0,[z0,z1,z2,z3,z867,z5]),(0,[z80,z1,z62,z2,z3,z5]),(0,[z0,z1,z2,z3,z717,z5])],[(0,[z0,z1,z2,z3,z4,z868]),(0,[z0,z1,z2,z3,z4,z869]),(0,[z0,z53,z281,z2,z3,z123]),(0,[z0,z1,z2,z3,z4,z122]),(0,[z0,z870,z2,z3,z4,z5])]],
   [[(0,[z190,z1,z780,z3,z4,z5]),(0,[z1,z2,z148,z4,z156,z5]),(0,[z0,z1,z2,z3,z4,z871]),(0,[z0,z1,z15,z176,z4,z32])],[(0,[z0,z872,z2,z3,z4,z5]),(0,[z0,z259,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z4,z873]),(0,[z874,z1,z2,z3,z4,z5]),(0,[z125,z0,z2,z3,z128,z5]),(0,[z0,z53,z2,z3,z826,z5])],[(0,[z0,z875,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z876]),(0,[z0,z1,z281,z3,z271,z4]),(0,[z877,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z84,z711])],[(0,[z0,z1,z2,z3,z878,z5]),(0,[z0,z1,z2,z3,z4,z879]),(0,[z0,z1,z388,z2,z3,z16]),(0,[z0,z1,z2,z3,z4,z880]),(0,[z881,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z832]),(0,[z0,z1,z2,z3,z114,z16]),(0,[z882,z1,z2,z3,z4,z5])],[(0,[z492,z45,z2,z3,z4,z5]),(0,[z883,z0,z528,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z336]),(0,[z0,z1,z2,z706,z216,z5]),(0,[z0,z1,z11,z2,z3,z83])],[(0,[z0,z1,z180,z3,z183,z5]),(0,[z0,z1,z59,z3,z4,z443]),(0,[z0,z1,z2,z3,z4,z884]),(0,[z0,z1,z27,z2,z216,z32])],[(0,[z1,z147,z780,z3,z4,z5]),(0,[z0,z1,z59,z3,z424,z5]),(0,[z0,z885,z2,z3,z4,z5])],[(0,[z0,z886,z2,z3,z4,z5]),(0,[z0,z1,z887,z2,z3,z4]),(0,[z0,z1,z266,z3,z4,z78]),(0,[z0,z1,z3,z4,z32,z763]),(0,[z726,z1,z2,z3,z4,z16])]],
   [[(0,[z0,z1,z584,z2,z4,z32]),(0,[z0,z1,z3,z96,z4,z16])],[(0,[z0,z1,z180,z3,z4,z298]),(0,[z0,z1,z2,z3,z4,z888])],[(0,[z0,z1,z2,z3,z4,z889]),(0,[z24,z1,z2,z3,z4,z634]),(0,[z0,z1,z890,z2,z3,z5]),(0,[z58,z0,z2,z232,z4,z16]),(0,[z604,z1,z2,z3,z4,z16]),(0,[z0,z1,z104,z3,z4,z5]),(0,[z0,z1,z487,z3,z4,z16])],[(0,[z1,z2,z3,z4,z749,z5]),(0,[z0,z1,z2,z3,z4,z891])],[(0,[z0,z1,z2,z3,z892,z5]),(0,[z0,z1,z180,z3,z87,z5]),(0,[z0,z1,z893,z3,z4,z5]),(0,[z1,z2,z3,z4,z894,z5]),(0,[z0,z1,z2,z4,z316,z32]),(0,[z0,z1,z895,z2,z3,z4]),(0,[z847,z1,z2,z3,z4,z5]),(0,[z0,z1,z30,z473,z4,z5]),(0,[z0,z1,z29,z166,z171,z3]),(0,[z0,z1,z2,z4,z493,z32]),(0,[z0,z1,z2,z717,z216,z5]),(0,[z0,z170,z2,z3,z4,z488])],[(0,[z1,z45,z388,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z896]),(0,[z0,z1,z2,z21,z4,z16]),(0,[z0,z1,z2,z4,z16,z402])],[(0,[z1,z735,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z897]),(0,[z0,z1,z29,z3,z130,z5])],[(0,[z0,z1,z898,z2,z3,z4]),(0,[z0,z1,z899,z3,z4,z5]),(0,[z108,z1,z578,z2,z3,z4]),(0,[z0,z2,z3,z826,z123,z5])]],
   [[(0,[z24,z1,z2,z3,z4,z290]),(0,[z0,z1,z2,z3,z900,z5]),(0,[z0,z1,z2,z3,z5,z769]),(0,[z0,z1,z901,z3,z4,z5]),(0,[z0,z1,z30,z3,z276,z5]),(0,[z0,z1,z3,z96,z4,z343])],[(0,[z270,z45,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z902,z4]),(0,[z0,z1,z62,z554,z3,z5]),(0,[z24,z1,z2,z3,z4,z894]),(0,[z0,z1,z2,z3,z4,z903])],[(0,[z0,z1,z2,z3,z5,z904]),(0,[z0,z1,z2,z3,z5,z905]),(0,[z0,z1,z27,z2,z216,z254]),(0,[z0,z1,z487,z3,z4,z343])],[(0,[z0,z1,z2,z3,z4,z906]),(0,[z0,z907,z528,z2,z3,z4]),(1,[z1,z2,z3,z749,z5]),(0,[z0,z1,z2,z3,z23,z711])],[(0,[z0,z1,z2,z3,z4,z908]),(0,[z0,z1,z909,z3,z4,z5]),(0,[z409,z1,z140,z3,z4,z5]),(0,[z58,z0,z2,z232,z4,z200]),(0,[z0,z1,z2,z3,z4,z910]),(0,[z0,z1,z2,z3,z4,z809]),(0,[z0,z911,z2,z3,z4,z32]),(0,[z912,z1,z2,z3,z4,z32])],[(0,[z0,z1,z2,z3,z913,z5]),(0,[z0,z1,z317,z3,z63,z5]),(0,[z0,z1,z2,z3,z914,z4]),(0,[z0,z1,z15,z176,z4,z5]),(0,[z0,z1,z11,z2,z3,z32])],[(0,[z0,z1,z2,z3,z915,z5]),(0,[z0,z1,z916,z2,z3,z4]),(0,[z0,z1,z2,z3,z826,z5]),(0,[z265,z0,z2,z3,z4,z32])],[(0,[z0,z1,z2,z3,z917,z5]),(0,[z0,z918,z2,z3,z4,z5]),(0,[z0,z919,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z920]),(0,[z0,z1,z166,z11,z3,z5]),(0,[z0,z1,z104,z3,z84,z5])]],
   [[(0,[z239,z1,z780,z3,z4,z5]),(0,[z218,z259,z2,z3,z4,z5]),(0,[z0,z329,z180,z3,z4,z5]),(0,[z0,z270,z2,z3,z4,z32]),(0,[z827,z471,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z921]),(0,[z0,z1,z140,z3,z424,z5]),(0,[z0,z1,z30,z113,z114,z5]),(0,[z0,z922,z2,z3,z4,z5])],[(0,[z681,z65,z2,z3,z4,z5]),(0,[z0,z1,z923,z2,z3,z4]),(0,[z0,z859,z427,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z924]),(0,[z471,z1,z2,z3,z4,z16]),(0,[z265,z0,z29,z3,z4,z5])],[(0,[z135,z1,z2,z3,z99,z185]),(0,[z0,z73,z3,z649,z4,z5]),(0,[z0,z1,z2,z3,z4,z925]),(0,[z0,z1,z27,z2,z216,z5])],[(0,[z0,z1,z2,z3,z926,z5]),(0,[z0,z1,z2,z345,z4,z32]),(0,[z152,z1,z2,z3,z424,z5]),(0,[z0,z1,z2,z3,z306,z32]),(0,[z0,z1,z11,z3,z38,z5]),(0,[z0,z1,z927,z2,z3,z4])],[(0,[z10,z65,z2,z3,z4,z5]),(0,[z190,z1,z147,z3,z4,z16]),(0,[z0,z1,z2,z3,z124,z4]),(0,[z0,z1,z2,z3,z5,z794])],[(0,[z0,z928,z2,z3,z4,z5]),(0,[z0,z1,z929,z3,z4,z5]),(0,[z0,z1,z2,z3,z23,z704])],[(0,[z0,z1,z29,z3,z187,z5]),(0,[z0,z1,z2,z3,z4,z930]),(0,[z0,z53,z2,z3,z123,z16]),(0,[z931,z1,z2,z3,z4,z5]),(0,[z0,z1,z30,z113,z4,z16]),(0,[z0,z1,z2,z3,z273,z220])],[(0,[z135,z1,z245,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z183,z32]),(0,[z0,z1,z2,z932,z4,z5]),(0,[z0,z1,z2,z3,z4,z933]),(0,[z0,z1,z166,z11,z3,z78])],[(0,[z10,z1,z2,z3,z4,z16])],[(0,[z0,z1,z2,z3,z4,z934]),(0,[z935,z1,z2,z3,z4,z5]),(0,[z936,z1,z2,z3,z4,z5]),(0,[z0,z1,z937,z2,z3,z4])],[(0,[z0,z1,z388,z3,z176,z5]),(0,[z0,z1,z116,z106,z2,z3]),(0,[z0,z660,z2,z3,z4,z16]),(0,[z0,z1,z275,z3,z183,z5]),(0,[z0,z2,z14,z723,z4,z5])],[(0,[z602,z45,z2,z3,z4,z5]),(0,[z24,z0,z1,z104,z3,z4]),(0,[z938,z1,z2,z3,z4,z5]),(0,[z939,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z124,z271,z4]),(1,[z0,z1,z29,z22,z3])],[(0,[z0,z1,z2,z3,z4,z940]),(0,[z1,z2,z3,z4,z894,z289]),(0,[z0,z110,z73,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z941]),(0,[z0,z1,z2,z621,z4,z16])],[(0,[z0,z109,z3,z383,z4,z5]),(0,[z0,z77,z2,z3,z4,z494]),(0,[z0,z1,z29,z3,z381,z5]),(0,[z942,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z943]),(0,[z0,z1,z2,z3,z87,z32]),(0,[z0,z944,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z945]),(0,[z0,z1,z3,z4,z38,z727]),(0,[z394,z1,z2,z3,z4,z350])]],
   [[(0,[z0,z1,z59,z3,z4,z16]),(0,[z0,z72,z2,z14,z4,z219]),(0,[z0,z1,z2,z3,z946,z4])],[(0,[z0,z911,z2,z3,z4,z5]),(0,[z320,z1,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z947]),(0,[z0,z1,z2,z3,z4,z948]),(0,[z58,z0,z59,z232,z4,z5]),(0,[z912,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z949,z4,z5]),(0,[z0,z1,z2,z3,z950,z5]),(0,[z0,z1,z22,z3,z150,z4])],[(0,[z0,z1,z275,z3,z87,z5]),(0,[z0,z1,z2,z3,z4,z951]),(0,[z952,z1,z2,z3,z4,z5]),(0,[z0,z1,z953,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z954]),(0,[z955,z165,z1,z2,z3,z4]),(0,[z0,z1,z11,z2,z3,z5]),(0,[z0,z1,z171,z2,z3,z83])],[(0,[z0,z1,z2,z3,z956,z4]),(0,[z0,z1,z957,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z958]),(0,[z0,z1,z959,z2,z3,z5]),(0,[z0,z1,z2,z3,z960,z5]),(0,[z0,z1,z2,z3,z4,z961]),(0,[z265,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z962]),(0,[z0,z1,z2,z4,z16,z772])],[(0,[z0,z1,z2,z3,z183,z298])],[(0,[z0,z270,z2,z3,z4,z5]),(0,[z0,z72,z2,z601,z4,z5]),(0,[z0,z2,z14,z35,z4,z5]),(0,[z0,z1,z356,z2,z4,z32]),(0,[z0,z1,z15,z176,z4,z426])],[(0,[z641,z1,z2,z64,z4,z5]),(0,[z404,z45,z2,z3,z4,z5]),(0,[z963,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z964]),(0,[z0,z1,z29,z3,z41,z129])],[(0,[z283,z224,z45,z2,z3,z4]),(0,[z0,z1,z2,z3,z183,z355]),(0,[z0,z2,z3,z965,z4,z5]),(0,[z0,z1,z2,z3,z966,z5]),(0,[z0,z72,z2,z723,z4,z5]),(0,[z967,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z234,z32])]],
   [[(0,[z24,z51,z2,z3,z4,z5]),(0,[z51,z2,z3,z4,z119,z5]),(0,[z13,z0,z722,z3,z4,z5]),(0,[z0,z1,z2,z3,z306,z5]),(0,[z0,z1,z526,z2,z216,z5]),(0,[z0,z1,z2,z3,z4,z968]),(0,[z0,z77,z2,z3,z4,z169]),(0,[z0,z2,z3,z175,z4,z16]),(0,[z0,z1,z166,z3,z111,z78]),(0,[z0,z1,z2,z3,z23,z518])],[(0,[z0,z969,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z970]),(0,[z126,z1,z2,z3,z141,z16]),(0,[z0,z1,z2,z303,z63,z32])],[(0,[z385,z45,z2,z3,z4,z5]),(0,[z0,z1,z971,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z136]),(0,[z0,z1,z59,z3,z4,z200]),(1,[z0,z1,z2,z4,z772])],[(0,[z0,z1,z2,z3,z4,z972]),(0,[z0,z1,z2,z3,z973,z5]),(0,[z0,z1,z2,z3,z4,z974]),(0,[z0,z329,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z87,z298])],[(0,[z0,z975,z2,z3,z4,z5]),(0,[z24,z1,z157,z2,z3,z4]),(1,[z0,z2,z3,z826,z5]),(0,[z0,z1,z2,z3,z276,z16]),(0,[z0,z1,z166,z3,z131,z4]),(0,[z0,z1,z2,z3,z4,z727]),(0,[z976,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z977]),(0,[z0,z1,z2,z3,z978,z5]),(0,[z0,z1,z2,z3,z183,z5]),(0,[z24,z1,z277,z2,z3,z4]),(0,[z0,z1,z979,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z980])],[(0,[z190,z660,z147,z3,z4,z5]),(0,[z0,z1,z2,z3,z87,z355]),(0,[z394,z1,z2,z3,z4,z289]),(0,[z981,z1,z2,z3,z4,z5]),(0,[z0,z1,z317,z3,z4,z32]),(0,[z0,z2,z3,z175,z4,z982]),(0,[z0,z1,z29,z3,z260,z5])],[(0,[z883,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z983,z4]),(0,[z80,z1,z2,z3,z4,z16])]],
   [[(0,[z1,z2,z3,z99,z552,z5]),(0,[z0,z1,z984,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z985]),(0,[z0,z1,z2,z3,z4,z986]),(0,[z0,z2,z3,z4,z759,z5]),(0,[z0,z987,z2,z3,z4,z5])],[(0,[z988,z1,z2,z3,z4,z5]),(0,[z0,z1,z90,z2,z4,z772]),(0,[z0,z1,z2,z3,z23,z84])],[(0,[z86,z1,z2,z822,z4,z5]),(0,[z0,z722,z95,z3,z4,z5])],[(0,[z0,z329,z2,z3,z183,z5]),(0,[z0,z1,z140,z3,z4,z5]),(0,[z58,z0,z140,z232,z4,z5]),(1,[z0,z1,z2,z717,z5]),(0,[z0,z1,z989,z2,z3,z32])],[(0,[z334,z1,z2,z3,z99,z5]),(0,[z0,z1,z2,z990,z4,z5]),(0,[z0,z1,z2,z3,z87,z5]),(0,[z0,z1,z2,z3,z991,z4]),(0,[z0,z1,z3,z271,z4,z16]),(0,[z265,z0,z3,z150,z4,z5]),(0,[z0,z1,z29,z3,z41,z16]),(0,[z1,z2,z3,z4,z32,z992]),(0,[z0,z1,z461,z2,z4,z32])],[(0,[z0,z45,z2,z3,z4,z555]),(0,[z0,z1,z993,z2,z3,z5]),(0,[z126,z259,z2,z3,z4,z5]),(0,[z0,z1,z317,z3,z216,z5]),(0,[z955,z0,z1,z2,z3,z4]),(0,[z0,z1,z3,z4,z727,z78]),(0,[z0,z1,z25,z3,z4,z549]),(0,[z0,z1,z856,z3,z4,z16])],[(0,[z320,z1,z2,z3,z4,z5]),(0,[z0,z994,z2,z3,z4,z5]),(0,[z0,z528,z2,z3,z4,z32]),(0,[z0,z995,z2,z3,z4,z5]),(0,[z0,z1,z104,z3,z4,z129]),(0,[z0,z1,z861,z3,z4,z16])],[(0,[z239,z1,z117,z3,z4,z32]),(0,[z0,z329,z2,z3,z4,z298]),(0,[z152,z2,z3,z232,z4,z5]),(0,[z0,z1,z2,z3,z4,z996])]],
   [[(0,[z0,z1,z997,z3,z4,z5]),(0,[z0,z1,z180,z3,z4,z32]),(0,[z0,z1,z998,z2,z3,z4]),(0,[z0,z1,z171,z435,z2,z3])],[(0,[z283,z0,z51,z2,z3,z4]),(0,[z0,z1,z999,z3,z4,z5]),(0,[z0,z1,z2,z3,z308,z84]),(0,[z107,z0,z2,z3,z4,z759]),(0,[z1000,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z188]),(0,[z0,z1001,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1002,z4]),(0,[z0,z1,z2,z3,z4,z1003]),(0,[z0,z1004,z2,z3,z4,z5]),(0,[z0,z329,z2,z3,z87,z5])],[(0,[z0,z1,z2,z3,z4,z1005]),(0,[z125,z0,z2,z3,z128,z16])],[(0,[z0,z1,z2,z3,z1006,z5]),(0,[z0,z1,z29,z3,z452,z5]),(0,[z877,z1,z2,z3,z4,z16])],[(0,[z0,z1,z1007,z2,z3,z5]),(0,[z0,z1,z11,z25,z2,z3]),(0,[z1,z2,z3,z4,z132,z32])],[(0,[z0,z1,z115,z176,z4,z5]),(0,[z0,z1,z2,z3,z4,z1008]),(0,[z0,z1009,z2,z3,z4,z5]),(0,[z1010,z1,z2,z3,z4,z5]),(0,[z0,z1,z62,z3,z150,z32]),(0,[z0,z1,z2,z303,z63,z5])],[(0,[z18,z65,z2,z3,z4,z32]),(0,[z125,z0,z2,z3,z696,z5]),(0,[z0,z1,z2,z3,z4,z335]),(0,[z0,z73,z722,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1011])]],
   [[(0,[z641,z0,z2,z232,z4,z5]),(0,[z283,z0,z77,z2,z3,z4]),(0,[z24,z1,z2,z3,z4,z289]),(0,[z1012,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1013]),(0,[z0,z1,z2,z3,z1014,z4]),(0,[z0,z1,z2,z1015,z3,z4])],[(0,[z100,z45,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1016]),(0,[z0,z1,z1017,z3,z4,z5]),(0,[z0,z1,z3,z1018,z4,z5]),(0,[z0,z1,z2,z3,z4,z1019]),(0,[z409,z1,z2,z3,z4,z32]),(0,[z0,z1,z30,z113,z276,z5]),(0,[z0,z1,z62,z3,z5,z285])],[(0,[z0,z1,z1020,z3,z4,z5]),(0,[z0,z1,z2,z3,z1021,z4]),(0,[z0,z1,z2,z3,z4,z1022]),(0,[z0,z77,z51,z2,z3,z4]),(0,[z1023,z1,z2,z3,z4,z5]),(0,[z0,z1024,z2,z3,z4,z32])],[(0,[z0,z735,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1025]),(0,[z0,z1,z1026,z2,z3,z5]),(0,[z218,z1,z2,z148,z4,z32]),(0,[z0,z1,z317,z3,z4,z5]),(0,[z0,z1,z762,z176,z4,z5]),(0,[z0,z1,z598,z176,z4,z5]),(0,[z0,z1,z2,z3,z4,z1027])],[(0,[z409,z1,z2,z3,z306,z5]),(0,[z0,z1,z2,z3,z4,z1028]),(0,[z0,z1,z29,z387,z3,z5]),(0,[z0,z1,z104,z3,z4,z16])],[(0,[z0,z1,z1029,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z1030]),(0,[z0,z1,z2,z3,z424,z32]),(0,[z0,z1,z2,z3,z4,z496]),(0,[z0,z1,z2,z3,z4,z1031]),(0,[z1,z2,z3,z4,z5,z992])],[(0,[z0,z1,z1032,z3,z4,z5]),(0,[z0,z1,z1033,z3,z4,z5]),(0,[z165,z1,z2,z3,z4,z32]),(0,[z0,z1,z15,z762,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1034]),(0,[z0,z1,z180,z3,z4,z355]),(0,[z0,z1,z2,z3,z1035,z5]),(0,[z0,z1,z2,z3,z1036,z5]),(0,[z0,z1,z2,z3,z306,z443]),(0,[z0,z77,z396,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1037]),(0,[z0,z1,z487,z3,z63,z5])]],
   [[(0,[z0,z1,z2,z3,z1038,z5]),(0,[z0,z1,z989,z2,z3,z5])],[(0,[z0,z1,z204,z2,z3,z4]),(0,[z218,z1,z2,z148,z4,z287]),(0,[z1039,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z219]),(0,[z0,z53,z3,z271,z123,z5]),(0,[z0,z1,z2,z55,z4,z772])],[(0,[z0,z1,z2,z3,z1040,z5]),(0,[z0,z1,z2,z3,z4,z1041]),(0,[z0,z72,z2,z14,z4,z154]),(0,[z0,z1,z2,z480,z4,z16])],[(0,[z0,z528,z2,z3,z4,z5]),(0,[z0,z1,z1042,z3,z4,z5]),(0,[z0,z1,z2,z3,z1043,z5]),(0,[z0,z1,z1044,z3,z4,z5]),(0,[z0,z1,z1045,z3,z4,z5])],[(0,[z0,z1,z1046,z3,z4,z5]),(0,[z239,z1,z117,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1047]),(0,[z107,z0,z1,z11,z2,z3]),(0,[z0,z1,z2,z3,z4,z1048]),(0,[z0,z1,z2,z3,z4,z1049])],[(0,[z0,z1,z180,z3,z4,z5]),(0,[z0,z1,z2,z3,z1050,z5]),(0,[z80,z1,z2,z3,z99,z5]),(0,[z0,z1,z3,z4,z739,z5]),(1,[z0,z1,z2,z3,z711])],[(0,[z0,z1,z2,z3,z4,z1051]),(0,[z18,z582,z2,z3,z4,z5]),(0,[z295,z1,z2,z3,z99,z5]),(0,[z0,z2,z3,z4,z1052,z5]),(0,[z778,z1,z2,z3,z4,z5])],[(0,[z0,z1,z1053,z3,z4,z5]),(0,[z0,z1,z116,z2,z3,z4]),(0,[z0,z1054,z2,z3,z4,z5]),(0,[z0,z1,z2,z525,z4,z32]),(0,[z108,z1,z2,z3,z4,z687]),(0,[z0,z1,z3,z150,z412,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z1055]),(0,[z0,z226,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z257]),(0,[z0,z1,z2,z4,z16,z581])],[(0,[z0,z1,z2,z822,z4,z5]),(0,[z0,z1,z3,z1056,z4,z5]),(0,[z1057,z1,z2,z3,z4,z32])],[(0,[z0,z1,z2,z3,z4,z1058]),(0,[z1,z2,z3,z4,z132,z5]),(0,[z0,z1,z140,z3,z4,z443])],[(0,[z18,z1,z388,z2,z3,z5]),(0,[z108,z279,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1059]),(0,[z0,z1,z62,z3,z150,z5])],[(0,[z18,z65,z2,z3,z4,z5]),(0,[z0,z1,z27,z2,z216,z16])],[(0,[z152,z1,z2,z3,z4,z443]),(0,[z265,z1060,z2,z3,z4,z5])],[(0,[z409,z1,z2,z3,z4,z5]),(0,[z0,z1,z275,z3,z4,z32]),(0,[z0,z1,z1061,z2,z3,z5]),(0,[z1062,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1063]),(0,[z0,z1,z2,z3,z4,z1064]),(0,[z0,z1,z11,z2,z3,z129]),(0,[z0,z1,z1065,z2,z3,z4])],[(0,[z0,z1,z2,z3,z5,z1066]),(0,[z0,z1,z2,z3,z4,z1067]),(0,[z0,z77,z2,z3,z4,z79]),(0,[z0,z1024,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z1068,z5]),(0,[z218,z1,z2,z148,z4,z5]),(0,[z0,z1,z2,z3,z1069,z5])],[(0,[z1070,z0,z1,z2,z3,z4]),(0,[z0,z752,z2,z3,z4,z5])],[(0,[z0,z1071,z2,z3,z4,z5]),(0,[z0,z1,z2,z359,z4,z16]),(0,[z0,z1,z2,z3,z424,z5])],[(0,[z165,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1072]),(0,[z135,z1,z2,z3,z99,z335]),(0,[z58,z152,z2,z232,z4,z5]),(0,[z0,z1,z29,z22,z3,z41]),(0,[z0,z1,z2,z3,z16,z111]),(0,[z0,z1073,z2,z3,z4,z5])],[(0,[z283,z0,z2,z3,z4,z66]),(0,[z0,z1,z1074,z2,z3,z4]),(0,[z0,z53,z2,z3,z124,z123]),(0,[z1,z2,z3,z4,z1075,z5]),(0,[z1076,z0,z2,z3,z4,z5]),(0,[z0,z1,z166,z3,z4,z129]),(0,[z0,z1,z2,z4,z5,z772]),(0,[z0,z1,z104,z171,z2,z3])],[(0,[z0,z1077,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1078,z5]),(0,[z0,z1,z2,z3,z4,z1079])],[(0,[z0,z1080,z2,z3,z4,z5]),(0,[z0,z427,z2,z3,z4,z32]),(0,[z152,z72,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1081]),(0,[z0,z1,z376,z3,z4,z78]),(0,[z0,z1,z2,z55,z4,z16])],[(0,[z0,z1,z2,z3,z4,z894]),(0,[z0,z1,z1082,z2,z3,z4]),(0,[z0,z1,z29,z3,z377,z5]),(0,[z0,z1,z2,z3,z84,z262])]],
   [[(0,[z10,z45,z2,z3,z4,z5]),(0,[z86,z1,z2,z64,z183,z5]),(0,[z0,z1,z2,z3,z1083,z5]),(0,[z0,z1,z2,z3,z4,z1084]),(0,[z0,z1,z1085,z3,z4,z5]),(0,[z0,z1,z2,z3,z23,z220]),(0,[z0,z1,z2,z3,z344,z84])],[(0,[z0,z1,z2,z3,z4,z1086]),(0,[z0,z1,z29,z3,z84,z38])],[(0,[z0,z1,z1087,z3,z4,z5]),(0,[z0,z1,z275,z3,z4,z298]),(0,[z0,z1,z2,z1088,z4,z5])],[(0,[z24,z77,z45,z2,z3,z4]),(0,[z0,z1,z2,z3,z1089,z5]),(0,[z0,z1,z2,z3,z4,z1090]),(0,[z0,z1,z2,z3,z4,z759])],[(0,[z45,z2,z3,z4,z589,z5]),(0,[z86,z1,z2,z64,z4,z298]),(0,[z0,z1,z1091,z2,z3,z4]),(0,[z0,z1,z11,z2,z3,z16]),(0,[z0,z1,z171,z3,z258,z83])],[(0,[z0,z226,z2,z3,z4,z5]),(0,[z0,z1,z1092,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1093]),(0,[z0,z1,z275,z3,z4,z355]),(0,[z125,z0,z2,z3,z826,z5]),(0,[z0,z1,z2,z662,z63,z5]),(0,[z265,z0,z2,z3,z4,z16])],[(0,[z0,z1,z2,z3,z4,z1094]),(0,[z0,z1,z2,z3,z1095,z5]),(0,[z0,z77,z445,z2,z3,z4]),(0,[z0,z1,z3,z4,z1096,z5]),(0,[z1057,z1,z2,z3,z4,z5])],[(0,[z0,z1,z780,z3,z4,z5]),(0,[z0,z259,z2,z3,z183,z5]),(0,[z86,z1,z2,z64,z87,z5]),(0,[z218,z1,z2,z822,z4,z5]),(0,[z1,z2,z148,z822,z4,z5]),(0,[z0,z270,z2,z3,z4,z16]),(0,[z0,z1,z375,z2,z3,z83])]],
   [[(0,[z0,z1,z2,z3,z4,z32]),(0,[z0,z1,z1097,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1098]),(0,[z0,z51,z2,z3,z4,z32]),(0,[z1099,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1100]),(0,[z0,z1,z1101,z3,z4,z5]),(0,[z0,z1,z2,z3,z1102,z5]),(0,[z0,z1,z3,z762,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1103]),(0,[z0,z1,z2,z3,z306,z16]),(0,[z1104,z0,z1,z2,z3,z4]),(0,[z0,z1,z317,z281,z3,z4]),(0,[z0,z1,z2,z4,z563,z32])],[(0,[z0,z1,z275,z3,z4,z5]),(0,[z0,z1,z166,z181,z3,z4]),(0,[z58,z0,z2,z232,z306,z5]),(0,[z279,z1,z2,z3,z4,z32])],[(0,[z18,z330,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1105]),(0,[z0,z1,z1106,z2,z3,z4]),(0,[z0,z1,z281,z2,z3,z4]),(0,[z0,z1,z3,z4,z5,z1107]),(0,[z1060,z1,z2,z3,z4,z5]),(0,[z1108,z1,z2,z3,z4,z5]),(0,[z0,z1,z171,z2,z3,z319])],[(0,[z0,z1,z3,z1109,z4,z5]),(0,[z0,z1,z3,z150,z739,z5]),(0,[z0,z1,z2,z303,z63,z481])],[(0,[z0,z1,z2,z1110,z4,z5]),(0,[z0,z1,z2,z3,z4,z1111]),(0,[z0,z1112,z2,z3,z4,z5]),(0,[z0,z259,z2,z3,z87,z5]),(0,[z0,z1,z2,z3,z4,z287]),(0,[z0,z1,z2,z3,z1113,z5]),(0,[z0,z1,z2,z3,z1114,z5]),(0,[z393,z0,z2,z3,z128,z5]),(0,[z0,z1,z2,z145,z4,z16])],[(0,[z0,z1,z2,z3,z183,z16]),(0,[z58,z0,z2,z723,z4,z5]),(0,[z0,z1,z487,z3,z216,z5]),(0,[z0,z1,z1115,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z1116]),(0,[z1039,z471,z1,z2,z3,z4]),(0,[z0,z2,z3,z723,z4,z5]),(0,[z0,z1,z3,z4,z16,z258])],[(0,[z0,z329,z275,z3,z4,z5]),(0,[z1,z2,z3,z4,z119,z894]),(0,[z0,z1,z29,z3,z41,z336]),(0,[z1,z2,z3,z4,z132,z1117])],[(0,[z0,z1,z29,z586,z3,z5])],[(0,[z0,z427,z2,z3,z4,z5]),(0,[z18,z660,z2,z3,z4,z5]),(0,[z320,z65,z2,z3,z4,z5]),(0,[z86,z329,z2,z64,z4,z5]),(0,[z0,z1,z2,z3,z4,z154])],[(0,[z0,z1,z2,z3,z4,z298]),(0,[z1118,z1,z2,z3,z4,z5]),(0,[z0,z1,z25,z3,z4,z189])],[(0,[z0,z1,z2,z3,z4,z1119]),(0,[z0,z1,z2,z3,z4,z1120]),(0,[z0,z1,z1121,z2,z3,z5]),(0,[z409,z1,z2,z3,z4,z443]),(0,[z0,z1,z140,z3,z4,z16]),(0,[z0,z1,z1122,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z254])],[(0,[z0,z1,z2,z3,z87,z16]),(0,[z0,z1123,z2,z3,z4,z5]),(0,[z0,z1,z1124,z3,z4,z5]),(0,[z0,z109,z722,z3,z4,z5]),(0,[z409,z1,z2,z3,z424,z5]),(0,[z1125,z165,z1,z2,z3,z4]),(0,[z107,z279,z2,z3,z4,z66]),(0,[z0,z1,z166,z387,z3,z4]),(0,[z0,z1,z303,z96,z63,z5]),(0,[z1126,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z355]),(0,[z0,z1,z2,z3,z1127,z5]),(0,[z1,z2,z3,z4,z1128,z5]),(0,[z0,z1,z2,z3,z4,z1129])]],
   [[(0,[z320,z1,z2,z3,z4,z16]),(0,[z152,z1,z2,z3,z4,z16])],[(0,[z0,z1,z2,z3,z1130,z5]),(0,[z0,z1,z2,z384,z4,z16]),(0,[z0,z1,z2,z3,z424,z443]),(0,[z0,z1,z2,z3,z4,z1131])],[(0,[z531,z1,z117,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1132]),(0,[z0,z1,z1133,z2,z3,z4]),(1,[z0,z1,z166,z11,z3])],[(0,[z149,z65,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1134]),(0,[z108,z226,z2,z3,z4,z119]),(0,[z0,z1,z2,z3,z1135,z5]),(0,[z0,z170,z2,z3,z4,z169])],[(0,[z1136,z0,z1,z2,z3,z4]),(0,[z1,z2,z3,z4,z1137,z5]),(0,[z0,z1,z171,z2,z3,z129])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z329,z2,z3,z4,z355]),(0,[z0,z1,z395,z3,z4,z49]),(0,[z0,z1,z2,z455,z4,z16])],[(0,[z0,z51,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1138]),(0,[z0,z1,z2,z3,z4,z1139]),(0,[z0,z1,z2,z3,z1140,z5]),(0,[z0,z678,z2,z3,z123,z5]),(0,[z0,z1,z2,z762,z4,z5]),(0,[z0,z1,z3,z150,z5,z368]),(0,[z0,z1,z2,z4,z32,z595])],[(0,[z0,z1,z2,z3,z1141,z5]),(0,[z664,z45,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1142]),(0,[z10,z270,z2,z3,z4,z5]),(0,[z0,z1,z140,z3,z4,z200]),(0,[z0,z1,z2,z4,z16,z693])]],
   [[(0,[z279,z1,z2,z3,z4,z5]),(0,[z126,z1,z2,z3,z28,z5]),(0,[z0,z65,z317,z3,z4,z5]),(0,[z86,z1,z180,z64,z4,z5]),(0,[z0,z1,z2,z3,z4,z1143]),(0,[z0,z1144,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1145,z4]),(0,[z1146,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z303,z63,z16])],[(0,[z0,z1,z1147,z2,z3,z4]),(0,[z0,z907,z1,z2,z3,z4]),(1,[z0,z2,z3,z4,z759]),(0,[z0,z1,z2,z3,z114,z496]),(0,[z0,z1,z487,z303,z63,z5]),(0,[z1148,z1,z2,z3,z4,z5])],[(0,[z0,z1,z388,z204,z2,z3]),(0,[z0,z1149,z2,z3,z4,z5]),(0,[z152,z1,z2,z3,z4,z200]),(0,[z0,z72,z2,z14,z4,z32]),(0,[z0,z1,z2,z3,z4,z982]),(0,[z0,z1,z2,z3,z4,z1150]),(0,[z80,z1,z27,z2,z216,z5])],[(0,[z0,z329,z2,z3,z4,z5]),(0,[z58,z409,z2,z232,z4,z5]),(0,[z0,z1151,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1152])],[(0,[z1,z2,z3,z99,z749,z5]),(0,[z135,z1,z2,z3,z99,z32]),(0,[z108,z1,z2,z3,z4,z161]),(0,[z13,z152,z2,z3,z4,z5]),(0,[z0,z1,z30,z227,z4,z5])],[(1,[z735,z2,z3,z4,z5]),(0,[z0,z1153,z2,z3,z4,z5]),(0,[z1,z2,z3,z822,z4,z5]),(0,[z135,z1,z2,z3,z749,z5]),(0,[z0,z2,z722,z3,z4,z5]),(0,[z0,z1,z317,z3,z4,z16]),(0,[z0,z1,z2,z3,z4,z843]),(0,[z0,z1154,z2,z3,z4,z5])],[(0,[z1155,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z1156,z4,z5])],[(0,[z0,z259,z180,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1157]),(0,[z0,z1,z15,z176,z4,z122]),(0,[z0,z1,z113,z762,z4,z5]),(0,[z0,z1,z2,z3,z711,z83])]],
   [[(0,[z1158,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z303,z63,z343])],[(0,[z0,z1,z1159,z3,z4,z5]),(0,[z0,z1,z59,z3,z306,z5]),(0,[z1125,z0,z1,z2,z3,z4]),(0,[z0,z1,z1160,z2,z3,z4])],[(0,[z0,z1161,z2,z3,z4,z5]),(0,[z126,z1,z2,z3,z749,z5]),(0,[z0,z2,z3,z4,z32,z1162])],[(0,[z0,z1,z516,z2,z3,z4]),(0,[z1,z45,z2,z3,z4,z335]),(0,[z0,z1,z2,z1163,z3,z5]),(0,[z0,z1,z2,z3,z4,z1164]),(0,[z0,z1165,z2,z3,z4,z5]),(0,[z24,z1,z2,z3,z4,z333]),(0,[z1166,z1,z2,z3,z4,z5]),(0,[z0,z1,z1167,z3,z4,z5])],[(0,[z0,z1,z2,z1168,z4,z5]),(0,[z0,z1,z2,z425,z4,z32]),(0,[z0,z1,z2,z3,z114,z257])],[(0,[z0,z1169,z2,z3,z4,z5]),(0,[z0,z1,z30,z56,z4,z5]),(0,[z0,z528,z2,z3,z4,z16]),(0,[z1170,z1,z2,z3,z4,z5]),(0,[z0,z1,z29,z3,z739,z5])],[(0,[z239,z1,z117,z3,z4,z16]),(0,[z672,z1,z147,z3,z4,z5]),(0,[z125,z10,z2,z3,z128,z5]),(0,[z0,z1,z2,z3,z4,z1171])],[(0,[z0,z1,z2,z3,z4,z1172]),(0,[z0,z1,z180,z3,z4,z16]),(0,[z126,z270,z2,z3,z141,z5]),(0,[z91,z1,z2,z3,z4,z119]),(0,[z13,z320,z95,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1173]),(0,[z107,z0,z2,z3,z4,z31]),(0,[z0,z1,z62,z3,z477,z5])]],
   [[(0,[z0,z1,z1174,z2,z3,z4]),(0,[z0,z1,z3,z1175,z4,z5]),(0,[z0,z1,z2,z3,z4,z1176]),(0,[z0,z775,z2,z3,z4,z5]),(1,[z0,z1,z104,z171,z3])],[(0,[z224,z45,z2,z3,z4,z32]),(0,[z0,z1,z1177,z3,z4,z5]),(0,[z0,z1,z2,z3,z186,z83]),(0,[z1178,z1,z2,z3,z4,z5])],[(0,[z320,z660,z2,z3,z4,z5]),(0,[z0,z1,z2,z654,z4,z32]),(0,[z0,z1,z2,z3,z4,z1179]),(0,[z0,z1,z2,z3,z4,z1180]),(0,[z0,z1,z15,z176,z4,z16])],[(0,[z0,z1,z2,z3,z4,z1181]),(1,[z1,z2,z822,z4,z5]),(0,[z0,z1182,z2,z3,z4,z5]),(0,[z0,z1,z2,z12,z63,z5]),(0,[z0,z1,z29,z22,z2,z3])],[(0,[z0,z1,z1183,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1184]),(0,[z0,z1,z2,z3,z5,z111]),(0,[z1,z2,z3,z4,z132,z16])],[(0,[z1,z45,z204,z2,z3,z4]),(0,[z0,z1,z2,z3,z786,z5]),(0,[z0,z1,z2,z3,z4,z1185]),(0,[z0,z1,z2,z3,z4,z426]),(0,[z0,z1,z2,z3,z4,z1186]),(0,[z0,z1,z62,z3,z150,z16])],[(0,[z18,z65,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z1187,z5]),(0,[z265,z0,z140,z3,z4,z5]),(0,[z0,z1,z2,z3,z1188,z4]),(0,[z0,z1,z171,z2,z3,z627]),(0,[z351,z1,z2,z3,z4,z161]),(0,[z0,z1,z375,z2,z3,z347])],[(0,[z0,z1189,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1190]),(0,[z0,z1,z2,z3,z1191,z5]),(0,[z0,z1,z2,z3,z4,z1192]),(0,[z152,z1,z59,z3,z4,z5]),(0,[z0,z72,z2,z14,z4,z5]),(0,[z0,z1,z2,z3,z4,z1193]),(0,[z0,z1,z22,z2,z3,z4]),(0,[z0,z1,z62,z3,z739,z5])]],
   [[(0,[z409,z1,z2,z3,z4,z16]),(0,[z0,z1,z1194,z3,z4,z5]),(0,[z0,z1,z3,z4,z32,z258]),(0,[z0,z1,z104,z171,z3,z83])],[(0,[z0,z1,z1195,z3,z4,z5]),(0,[z283,z279,z1,z2,z3,z4]),(0,[z135,z1,z2,z3,z99,z5]),(0,[z13,z0,z95,z3,z4,z32]),(0,[z0,z1,z27,z2,z717,z5]),(0,[z0,z267,z2,z3,z4,z494]),(0,[z0,z1,z2,z3,z5,z711])],[(0,[z0,z1,z2,z3,z4,z1196]),(0,[z218,z1,z2,z148,z4,z16]),(0,[z0,z53,z317,z3,z123,z5]),(0,[z0,z1,z1197,z3,z4,z5]),(0,[z0,z1,z29,z3,z41,z32])],[(0,[z86,z1,z2,z64,z4,z32]),(0,[z0,z2,z3,z826,z4,z5]),(0,[z0,z2,z3,z4,z5,z1162]),(0,[z0,z1,z2,z3,z4,z1198])],[(0,[z0,z1,z1199,z2,z4,z5]),(0,[z0,z109,z73,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z443]),(0,[z0,z1,z2,z3,z424,z16]),(0,[z0,z1,z30,z762,z4,z5]),(0,[z0,z1,z30,z113,z4,z496]),(0,[z0,z1,z2,z3,z1200,z5]),(0,[z0,z1,z2,z3,z4,z1117]),(0,[z0,z1,z1201,z3,z4,z32])],[(0,[z0,z1,z2,z3,z1202,z5]),(0,[z0,z1,z2,z3,z4,z1203]),(0,[z0,z1,z2,z3,z4,z1204]),(0,[z0,z1,z106,z2,z3,z32]),(0,[z0,z1,z1205,z3,z4,z5]),(0,[z265,z0,z73,z3,z4,z5]),(0,[z58,z0,z2,z232,z424,z5]),(0,[z1206,z1,z2,z3,z4,z5]),(0,[z165,z1,z2,z3,z4,z16]),(0,[z0,z1,z3,z176,z276,z5]),(0,[z0,z1,z22,z62,z2,z3]),(0,[z0,z1073,z2,z3,z4,z16])],[(0,[z224,z516,z45,z2,z3,z4]),(0,[z450,z1,z117,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1207]),(0,[z0,z1,z1208,z3,z4,z5]),(0,[z86,z1,z275,z64,z4,z5]),(0,[z1076,z0,z2,z3,z4,z16]),(0,[z0,z1,z806,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1209,z4]),(0,[z0,z1,z2,z3,z4,z1210]),(0,[z13,z0,z140,z3,z4,z5]),(0,[z0,z1,z2,z3,z739,z5])]],
   [[(0,[z65,z735,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1211]),(0,[z0,z15,z175,z176,z4,z5]),(0,[z0,z1,z2,z3,z4,z209]),(0,[z0,z1,z2,z3,z4,z1212]),(0,[z0,z1,z2,z217,z4,z16])],[(1,[z1,z2,z3,z4,z894]),(0,[z0,z109,z73,z3,z4,z136]),(0,[z0,z1,z25,z3,z4,z38])],[(0,[z0,z284,z2,z3,z123,z5]),(0,[z0,z1,z2,z3,z4,z1213]),(0,[z0,z1,z2,z3,z4,z1214]),(0,[z0,z1215,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1216]),(0,[z0,z259,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z111,z32])],[(0,[z0,z1,z1217,z3,z4,z5]),(0,[z218,z1,z2,z148,z4,z198]),(0,[z125,z165,z2,z3,z128,z5]),(0,[z0,z1,z2,z3,z4,z1218])],[(0,[z190,z1,z698,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1219]),(0,[z0,z1,z388,z2,z3,z32]),(0,[z80,z1,z2,z3,z87,z5]),(0,[z0,z1,z2,z1220,z4,z5]),(0,[z0,z1,z2,z3,z114,z32]),(0,[z0,z1,z3,z4,z38,z129]),(0,[z0,z1,z2,z3,z4,z1221])],[(0,[z1222,z0,z2,z3,z4,z5]),(0,[z1158,z0,z427,z2,z3,z4]),(0,[z0,z259,z275,z3,z4,z5]),(0,[z0,z2,z723,z232,z4,z5])],[(0,[z224,z45,z2,z3,z4,z5]),(0,[z0,z65,z2,z3,z4,z555]),(0,[z0,z1,z2,z3,z1223,z5]),(0,[z0,z2,z3,z4,z759,z169]),(0,[z0,z1,z551,z3,z4,z189])],[(0,[z0,z550,z73,z3,z4,z5]),(0,[z0,z226,z2,z3,z4,z16]),(0,[z0,z1,z30,z113,z4,z257])]],
   [[(0,[z0,z1,z1224,z3,z4,z5]),(0,[z0,z1,z104,z3,z4,z38])],[(0,[z19,z45,z2,z3,z4,z5]),(0,[z0,z65,z281,z2,z3,z4]),(1,[z1,z780,z3,z4,z5]),(0,[z0,z1225,z2,z3,z4,z5]),(0,[z152,z1,z140,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z258]),(0,[z80,z1001,z2,z3,z4,z5]),(0,[z0,z1,z3,z96,z4,z32])],[(0,[z660,z45,z2,z3,z4,z5]),(0,[z86,z1,z2,z64,z4,z355]),(0,[z0,z1,z2,z3,z4,z1226]),(0,[z0,z1,z25,z3,z4,z727]),(0,[z0,z1,z2,z3,z4,z772]),(0,[z0,z1,z2,z3,z344,z410])],[(0,[z0,z1,z2,z1227,z4,z5]),(0,[z58,z0,z2,z232,z4,z32]),(0,[z0,z77,z1,z11,z2,z3]),(0,[z604,z1,z2,z3,z4,z32]),(0,[z107,z604,z2,z3,z4,z66]),(0,[z0,z2,z3,z4,z838,z5]),(0,[z0,z1,z487,z3,z4,z32])],[(0,[z1,z2,z3,z99,z87,z5]),(0,[z108,z1,z2,z3,z4,z894]),(0,[z0,z1,z2,z3,z4,z555]),(0,[z0,z1,z1228,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z481])],[(0,[z0,z1,z275,z3,z4,z16]),(0,[z126,z1,z605,z2,z3,z5]),(0,[z0,z1,z29,z22,z3,z4]),(0,[z0,z1,z166,z11,z2,z3]),(0,[z0,z1,z3,z4,z16,z824])],[(0,[z239,z1,z204,z117,z3,z4]),(0,[z1,z780,z2,z3,z4,z5]),(0,[z0,z259,z2,z3,z4,z298]),(0,[z13,z0,z95,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1229,z5]),(0,[z58,z0,z2,z244,z4,z5]),(0,[z0,z1,z2,z3,z4,z1230]),(0,[z0,z1,z29,z3,z41,z5]),(0,[z0,z1,z2,z506,z4,z16]),(0,[z1,z2,z3,z4,z851,z5])]],
   [[(0,[z86,z1,z2,z64,z4,z5]),(0,[z24,z279,z1,z2,z3,z4]),(0,[z0,z1,z2,z473,z63,z5])],[(0,[z0,z1,z2,z3,z4,z1231]),(0,[z0,z259,z2,z3,z4,z355]),(0,[z0,z109,z73,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z129]),(0,[z0,z1,z2,z515,z4,z32]),(0,[z0,z1,z1201,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1232]),(0,[z0,z1,z106,z2,z3,z5]),(0,[z0,z1233,z2,z3,z4,z5]),(0,[z126,z1,z2,z3,z87,z5]),(0,[z0,z1,z2,z40,z4,z32]),(0,[z0,z1,z1234,z2,z3,z4]),(0,[z0,z1,z2,z3,z276,z496]),(0,[z133,z0,z2,z3,z4,z31])],[(0,[z1235,z1,z2,z3,z4,z5]),(0,[z107,z0,z2,z3,z4,z594]),(0,[z265,z0,z15,z176,z4,z5])],[(0,[z239,z1,z116,z117,z3,z4]),(0,[z0,z1236,z2,z3,z4,z5]),(0,[z0,z1237,z2,z3,z4,z5])],[(0,[z341,z45,z2,z3,z4,z5]),(0,[z0,z1,z1238,z3,z4,z5]),(0,[z0,z427,z2,z3,z4,z16]),(0,[z126,z528,z2,z3,z141,z5]),(0,[z279,z77,z2,z3,z4,z5]),(0,[z0,z1,z395,z3,z4,z38])],[(0,[z0,z1,z1239,z3,z4,z5]),(0,[z0,z73,z140,z3,z4,z5]),(0,[z1240,z1,z2,z3,z4,z5]),(0,[z0,z1,z166,z3,z4,z42])],[(0,[z0,z259,z2,z3,z4,z5]),(0,[z0,z1,z1241,z2,z3,z4]),(0,[z13,z0,z357,z3,z4,z5]),(0,[z409,z1,z59,z3,z4,z5]),(0,[z1242,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z306,z200]),(0,[z1243,z1,z2,z3,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 524) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 524).take 530) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1054).take 206) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1260)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [524, 530, 206] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 107).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 213).take 43).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [107, 106, 43] = true :=
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

end PEqualNP.Outside.L_meta_38843

theorem PEqualNP.Outside.L_meta_38843 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38843.solve
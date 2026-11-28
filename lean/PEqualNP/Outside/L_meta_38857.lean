import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38857

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
  Nat.testBit (4276808936 * 2 ^ 32 + 4209041632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0010b38160dc6314#64 ++ 0x40010b38160dc631#64 ++ 0x5033f783e1fce73f#64 ++ 0xa5033f783e1fce73#64 : BitVec 256),
   (0x00c580b4b1c52948#64 ++ 0x800c580b4b1c5294#64 ++ 0xe1cd89fcf1c739cf#64 ++ 0x7e1cd89fcf1c739c#64 : BitVec 256),
   (0x160a0c0a060294a1#64 ++ 0x0160a0c0a060294a#64 ++ 0x7e0e0e0f1e07fffe#64 ++ 0xf7e0e0e0f1e07fff#64 : BitVec 256),
   (0x2b700fd01b683e0e#64 ++ 0x02b700fd01b683e0#64 ++ 0xbff00ff01ff83e0d#64 ++ 0xfbff00ff01ff83e0#64 : BitVec 256),
   (0x8defd0001db7c000#64 ++ 0x08defd0001db7c00#64 ++ 0xbffff0001fffc00b#64 ++ 0xebffff0001fffc00#64 : BitVec 256),
   (0x4fbf6f6fc0000000#64 ++ 0x04fbf6f6fc000000#64 ++ 0xcfffffffe0000007#64 ++ 0xfcfffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [6, 2]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [13, 9]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x5033f783e1fce73f 0xa5033f783e1fce73

def z1 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xa1cd89fcf1c318c1 0x5a1cd89fcf1c318c

def z2 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x7e0e0e0f1e07fffe 0xf7e0e0e0f1e07fff

def z3 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff00ff01ff83e0d 0xfbff00ff01ff83e0

def z4 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcfffffffe0000007 0xfcfffffffe000000

def z5 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffff0001fffc00b 0xebffff0001fffc00

def z6 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xe1cd89fcf1c739cf 0x7e1cd89fcf1c739c

def z7 : W := mkw 0x161a0f8a064ab6a5 0x0161a0f8a064ab6a 0x7e3e0f8f1fffffff 0xf7e3e0f8f1ffffff

def z8 : W := mkw 0x5faf4c6e860294a1 0x05faf4c6e860294a 0xafcc087c1e0318c0 0x5afcc087c1e0318c

def z9 : W := mkw 0xaf3a5f400e3ad606 0x0af3a5f400e3ad60 0x1e3276000e38c600 0x81e3276000e38c60

def z10 : W := mkw 0x0000808020c42100 0x00000808020c4210 0x40018180e1c4210f 0x240018180e1c4210

def z11 : W := mkw 0x00d5b3b5f1dd6b5c 0xc00d5b3b5f1dd6b5 0xf1fffffff1ffffff 0xff1fffffff1fffff

def z12 : W := mkw 0x02100f8002483604 0x002100f800248360 0x3e300f801ff83e0d 0xf3e300f801ff83e0

def z13 : W := mkw 0x0010038000482204 0x0001003800048220 0x0030018001f80001 0x00030018001f8000

def z14 : W := mkw 0x10000000060294a1 0x010000000060294a 0x200000001e0318c0 0x0200000001e0318c

def z15 : W := mkw 0x0000908020dc6314 0x40000908020dc631 0x1000000001fce738 0x01000000001fce73

def z16 : W := mkw 0x0b300f4000000000 0x00b300f400000000 0x8ff00ff000000005 0xf8ff00ff00000000

def z17 : W := mkw 0x448fe02fe0850140 0x8448fe02fe085014 0x400ff00fe00701c2 0x0400ff00fe00701c

def z18 : W := mkw 0x0960009019602808 0x0096000901960280 0xbff009f01ff8380d 0xfbff009f01ff8380

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000060300002734 0x0400006030000273

def z20 : W := mkw 0x0010230140000000 0x0001023014000000 0x4033f783e0000007 0xa4033f783e000000

def z21 : W := mkw 0x204000901b683e0e 0x0204000901b683e0 0x300000001ff83e08 0x0300000001ff83e0

def z22 : W := mkw 0x0000000004028000 0x0000000000402800 0x300000001e07c008 0x0300000001e07c00

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z24 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0x81f1f1f0e0000001 0x081f1f1f0e000000

def z25 : W := mkw 0xcfbfff6fc497c000 0x0cfbfff6fc497c00 0xcfffffffe007c007 0xfcfffffffe007c00

def z26 : W := mkw 0x8def40001d238000 0x08def40001d23800 0xbfce00001e07c00a 0xebfce00001e07c00

def z27 : W := mkw 0x0920000008200000 0x0092000000820000 0x1e3000000e380000 0x81e3000000e38000

def z28 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xfffffffffe07ffff 0xffffffffffe07fff

def z29 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xc1cd89fce1c00007 0x7c1cd89fce1c0000

def z30 : W := mkw 0x12102f8b624837b5 0x412102f8b624837b 0x40000f8fe0003ff4 0x140000f8fe0003ff

def z31 : W := mkw 0x0010038000482204 0x0001003800048220 0x1030078001f8260d 0xa1030078001f8260

def z32 : W := mkw 0x2b600c501b201c0a 0x02b600c501b201c0 0xafc008701e001800 0x5afc008701e00180

def z33 : W := mkw 0x0960900019b44000 0x00960900019b4400 0xbff3f0001ffcc00b 0xebff3f0001ffcc00

def z34 : W := mkw 0x4faf4c6e80000000 0x04faf4c6e8000000 0x8fcc087c00000000 0x58fcc087c0000000

def z35 : W := mkw 0x804090903df7e948 0x8804090903df7e94 0x300000001ffff9c8 0x0300000001ffff9c

def z36 : W := mkw 0x004000b4b1402948 0x8004000b4b140294 0xe1c009fcf1c039cd 0x7e1c009fcf1c039c

def z37 : W := mkw 0x00952325c0000000 0x000952325c000000 0xc1ffffffe0000007 0xfc1ffffffe000000

def z38 : W := mkw 0x0960000019200000 0x0096000001920000 0xbff000001ff80009 0xebff000001ff8000

def z39 : W := mkw 0x2b70bfd17bfc7f1e 0x42b70bfd17bfc7f1 0xfff3fff3fffcff3f 0xffff3fff3fffcff3

def z40 : W := mkw 0x160a0c0a020014a1 0x0160a0c0a020014a 0x4e0e0e0f00003ff6 0xf4e0e0e0f00003ff

def z41 : W := mkw 0x5faf4c6e860294a1 0x05faf4c6e860294a 0xffce0e7f1e07fffe 0xfffce0e7f1e07fff

def z42 : W := mkw 0x141ab38b64dee3b5 0x4141ab38b64dee3b 0x503ff78fe1ffe7ff 0xa503ff78fe1ffe7f

def z43 : W := mkw 0x0faf4c0a00000000 0x00faf4c0a0000000 0xcffffe0f00000007 0xfcffffe0f0000000

def z44 : W := mkw 0x0010030000000000 0x0001003000000000 0x0030078000000005 0xa003007800000000

def z45 : W := mkw 0x8dafd0000cb7c000 0x08dafd0000cb7c00 0x1e3ff0000e3fc002 0x81e3ff0000e3fc00

def z46 : W := mkw 0x22100fd002483e0e 0x022100fd002483e0 0x00000ff000003e04 0x100000ff000003e0

def z47 : W := mkw 0x0085002480000000 0x0008500248000000 0xc1cd89fce0000007 0x7c1cd89fce000000

def z48 : W := mkw 0x00d5b3b5f1dd6b5c 0xc00d5b3b5f1dd6b5 0x81f1f1f0e1f80001 0x081f1f1f0e1f8000

def z49 : W := mkw 0x161a3f0b461ad6b5 0x4161a3f0b461ad6b 0x7e3e7e0f1e3ffffe 0xf7e3e7e0f1e3ffff

def z50 : W := mkw 0x2b702fd15b683e0e 0x02b702fd15b683e0 0xfff3fff3fff83e0f 0xffff3fff3fff83e0

def z51 : W := mkw 0x2b600cd01b683e0e 0x02b600cd01b683e0 0xbfc008701ff83e08 0x5bfc008701ff83e0

def z52 : W := mkw 0x10000000040280a1 0x010000000040280a 0x000000000007c1f0 0x0000000000007c1f

def z53 : W := mkw 0x29f583f4b9ed2b4e 0x829f583f4b9ed2b4 0xe1fd89fcf1ff39cf 0x7e1fd89fcf1ff39c

def z54 : W := mkw 0x297003d019682a0e 0x0297003d019682a0 0xbff001f01ff80009 0xebff001f01ff8000

def z55 : W := mkw 0x00c5003491010848 0x800c500349101084 0xa1cc087c100318c0 0x5a1cc087c100318c

def z56 : W := mkw 0x4f3a6f4b40000000 0x04f3a6f4b4000000 0x8ff27ff300000005 0xf8ff27ff30000000

def z57 : W := mkw 0x89e5d00019b54000 0x089e5d00019b5400 0x81f1f00001f80001 0x081f1f00001f8000

def z58 : W := mkw 0x8d2a50000c32c000 0x08d2a50000c32c00 0x1e3270000e38c000 0x81e3270000e38c00

def z59 : W := mkw 0x3f7a0fda1f6abeaf 0x03f7a0fda1f6abea 0xbffc0ffc1ffb3ecd 0xfbffc0ffc1ffb3ec

def z60 : W := mkw 0x2970b3d179fc6b1e 0x42970b3d179fc6b1 0x81f1f1f0e1f80001 0x081f1f1f0e1f8000

def z61 : W := mkw 0x00d5b38171dd6314 0x400d5b38171dd631 0xf1fff783f1ffe73f 0xef1fff783f1ffe73

def z62 : W := mkw 0x0b300f4002001400 0x00b300f400200140 0xbff00ff01e003e0d 0xfbff00ff01e003e0

def z63 : W := mkw 0x10000000060294a1 0x010000000060294a 0x300000001e07fff8 0x0300000001e07fff

def z64 : W := mkw 0x6bf56ff5db683e0e 0x06bf56ff5db683e0 0xbff1fff0fff83e0d 0xfbff1fff0fff83e0

def z65 : W := mkw 0x9fef4c0a1f2394a1 0x09fef4c0a1f2394a 0xafcc080c1e0318c0 0x5afcc080c1e0318c

def z66 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x2e0c080c1e0318c0 0x52e0c080c1e0318c

def z67 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0x8ff3f7f3e0000001 0x88ff3f7f3e000000

def z68 : W := mkw 0x0000000000000000 0x0000000000000000 0x4002060300000006 0xa400206030000000

def z69 : W := mkw 0x8dfff3817dffe314 0x48dfff3817dffe31 0xbffff180ffffc00b 0xebffff180ffffc00

def z70 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0x81c181f0e1c00001 0x081c181f0e1c0000

def z71 : W := mkw 0x0085800000850000 0x0008580000085000 0x000d800000070002 0x0000d80000007000

def z72 : W := mkw 0x12000c0a020014a1 0x012000c0a020014a 0x40000e0f00003ff4 0x140000e0f00003ff

def z73 : W := mkw 0xcdeff02fddb7c000 0x0cdeff02fddb7c00 0xfffff00fffffc00b 0xefffff00fffffc00

def z74 : W := mkw 0x4fbfffefe0dc6314 0x44fbfffefe0dc631 0xdfffffffe1fce73f 0xfdfffffffe1fce73

def z75 : W := mkw 0x0000900000944000 0x0000090000094400 0x1000000001fcc008 0x01000000001fcc00

def z76 : W := mkw 0x8def40001d238000 0x08def40001d23800 0xafcc00001e030000 0x4afcc00001e03000

def z77 : W := mkw 0x89f5f38179fd6314 0x489f5f38179fd631 0x81f1f180e1f80001 0x081f1f180e1f8000

def z78 : W := mkw 0x0bb50f6480000000 0x00bb50f648000000 0xcffd8ffce0000007 0xfcffd8ffce000000

def z79 : W := mkw 0x00858024a0850140 0x800858024a085014 0x400d800ce00701c2 0x0400d800ce00701c

def z80 : W := mkw 0x848fd0000497c000 0x0848fd0000497c00 0x000ff0000007c002 0x0000ff0000007c00

def z81 : W := mkw 0x4fff6f6fd9200000 0x04fff6f6fd920000 0xfffffffffff8000f 0xffffffffffff8000

def z82 : W := mkw 0x00d5a3b5f1c52948 0x800d5a3b5f1c5294 0xe1fffffff1c739cf 0xfe1fffffff1c739c

def z83 : W := mkw 0x0daf400000000000 0x00daf40000000000 0x8fcc000000000000 0x48fcc00000000000

def z84 : W := mkw 0x060a0c0a00000000 0x0060a0c0a0000000 0x4e0e0e0f00000006 0xf4e0e0e0f0000000

def z85 : W := mkw 0x4fbfff6fe0944110 0x44fbfff6fe094411 0xcfffffffe004c137 0xfcfffffffe004c13

def z86 : W := mkw 0x160a9c8a26def7b5 0x4160a9c8a26def7b 0x7e0e0e0f1ffffffe 0xf7e0e0e0f1ffffff

def z87 : W := mkw 0x00c590b4b1d56948 0x800c590b4b1d5694 0xf1fff9fcf1fff9cf 0xff1fff9fcf1fff9c

def z88 : W := mkw 0x4f3a6f4b40000000 0x04f3a6f4b4000000 0x0e32760300000000 0x80e3276030000000

def z89 : W := mkw 0x4fffeffff1c52948 0x84fffeffff1c5294 0xeffffffff1c739cf 0xfeffffffff1c739c

def z90 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x5e0e060f0e07c7f2 0x85e0e060f0e07c7f

def z91 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x5e020e0f0e00fff4 0x95e020e0f0e00fff

def z92 : W := mkw 0x4fbf6fffe0402948 0x84fbf6fffe040294 0xcfffffffe00039c7 0xfcfffffffe00039c

def z93 : W := mkw 0x0040809031c52948 0x80040809031c5294 0x600c080c11c739ce 0x7600c080c11c739c

def z94 : W := mkw 0x16cf8cbeb7c7bde9 0x816cf8cbeb7c7bde 0xffcf8fffffc7ffff 0xfffcf8fffffc7fff

def z95 : W := mkw 0x12000c0a020014a1 0x012000c0a020014a 0x0000060300000630 0x0000006030000063

def z96 : W := mkw 0xafffdfd01ffffe0e 0x0afffdfd01ffffe0 0xbffffff01ffffe0f 0xfbffffff01ffffe0

def z97 : W := mkw 0x8d2a40000c228000 0x08d2a40000c22800 0x0e0000000e000000 0x00e0000000e00000

def z98 : W := mkw 0x0000000000000000 0x0000000000000000 0x500206030004e73e 0xa500206030004e73

def z99 : W := mkw 0x6fff6fffd9682a0e 0x06fff6fffd9682a0 0xcfffffffe1f80007 0xfcfffffffe1f8000

def z100 : W := mkw 0x968fdc0a0697d4a1 0x0968fdc0a0697d4a 0x7e0ffe0f1e07fffe 0xf7e0ffe0f1e07fff

def z101 : W := mkw 0x02c58cb4b3c53d48 0x802c58cb4b3c53d4 0xffcd8ffcffc73fcf 0xfffcd8ffcffc73fc

def z102 : W := mkw 0x468f6c2fc0000000 0x0468f6c2fc000000 0x4e0ffe0fe0000006 0xf4e0ffe0fe000000

def z103 : W := mkw 0x4dbf6365c0000000 0x04dbf6365c000000 0x8ffff1f0e0000003 0xe8ffff1f0e000000

def z104 : W := mkw 0x89f5f38179fd6314 0x489f5f38179fd631 0xd1f3f783e1fce73f 0xad1f3f783e1fce73

def z105 : W := mkw 0x060a0c0a00000000 0x0060a0c0a0000000 0x0e02060300000000 0x80e0206030000000

def z106 : W := mkw 0x168f8c2ea68795e1 0x8168f8c2ea68795e 0x7e0f8e0ffe07fffe 0xf7e0f8e0ffe07fff

def z107 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x6e0c0e0f1e033ff4 0x56e0c0e0f1e033ff

def z108 : W := mkw 0x8d3a73014c3ac214 0x48d3a73014c3ac21 0x1e3276030e38c630 0x81e3276030e38c63

def z109 : W := mkw 0x0010338140586214 0x4001033814058621 0x1032778301f8e63d 0xa1032778301f8e63

def z110 : W := mkw 0x140a000a040280a1 0x0140a000a040280a 0x600e080f1007f9fe 0x7600e080f1007f9f

def z111 : W := mkw 0x848fd024a497c140 0x8848fd024a497c14 0x400ff00ce007c1c2 0x0400ff00ce007c1c

def z112 : W := mkw 0x8defd0b4bdf7e948 0x88defd0b4bdf7e94 0xfffff9fcfffff9cf 0xffffff9fcfffff9c

def z113 : W := mkw 0xcfbf7f6fcc32c000 0x0cfbf7f6fcc32c00 0xdfffffffee38c007 0xfdfffffffee38c00

def z114 : W := mkw 0x5fbf6f6fc20014a1 0x05fbf6f6fc20014a 0xcfffffffe0003ff7 0xfcfffffffe0003ff

def z115 : W := mkw 0x0010238160482314 0x4001023816048231 0x50020783e004e73e 0xa50020783e004e73

def z116 : W := mkw 0x0010938020dc6314 0x40010938020dc631 0x1030078001fce73d 0xa1030078001fce73

def z117 : W := mkw 0x161abf8b66def7b5 0x4161abf8b66def7b 0x7e3fff8fffffffff 0xf7e3fff8ffffffff

def z118 : W := mkw 0x00c590b4b1dd6b5c 0xc00c590b4b1dd6b5 0xf1cd89fcf1ffffff 0x7f1cd89fcf1fffff

def z119 : W := mkw 0x0050b39171dc6b1c 0x40050b39171dc6b1 0xf1f3fff3f1fcff3f 0xff1f3fff3f1fcff3

def z120 : W := mkw 0x0def400019200000 0x00def40001920000 0xbffff0001ff8000b 0xebffff0001ff8000

def z121 : W := mkw 0x6b702fffdb683e0e 0x06b702fffdb683e0 0xfff00ffffff83e0d 0xffff00ffffff83e0

def z122 : W := mkw 0x0010230140000000 0x0001023014000000 0x0031f180e0000001 0x00031f180e000000

def z123 : W := mkw 0x041ab38164dee314 0x4041ab38164dee31 0x7e3ff783ffffe73f 0xe7e3ff783ffffe73

def z124 : W := mkw 0x0b302f4140000000 0x00b302f414000000 0xcff3fff3e0000007 0xfcff3fff3e000000

def z125 : W := mkw 0x160a9c0a0696d4a1 0x0160a9c0a0696d4a 0x7e3ffe0f1fffffff 0xf7e3ffe0f1ffffff

def z126 : W := mkw 0x161a2f8b664ab7b5 0x4161a2f8b664ab7b 0x7e0e0f8ffe07fffe 0xf7e0e0f8ffe07fff

def z127 : W := mkw 0x0040009011402808 0x0004000901140280 0xa1c009f011c0380d 0x7a1c009f011c0380

def z128 : W := mkw 0x040a000a00000000 0x0040a000a0000000 0x400e000f00000002 0x0400e000f0000000

def z129 : W := mkw 0x296000901b683e0e 0x0296000901b683e0 0xbff000001ff83e09 0xebff000001ff83e0

def z130 : W := mkw 0x0050039011482a0c 0x00050039011482a0 0xb1f00ff011f83e0d 0xfb1f00ff011f83e0

def z131 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xc1c181f0e1c4210f 0x2c1c181f0e1c4210

def z132 : W := mkw 0x9fefdc0a1fb7d4a1 0x09fefdc0a1fb7d4a 0xfffffe0f1fffffff 0xffffffe0f1ffffff

def z133 : W := mkw 0x0040809031c52948 0x80040809031c5294 0x60018180f1c739cf 0x260018180f1c739c

def z134 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x1e0206030e00c630 0x81e0206030e00c63

def z135 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0xc1fdf9fce0000007 0x7c1fdf9fce000000

def z136 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xf1cf8ffff1c7ffff 0xff1cf8ffff1c7fff

def z137 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xfffff6031fffe73f 0xefffff6031fffe73

def z138 : W := mkw 0x0000b00160944110 0x40000b0016094411 0x4003f003e004c132 0x04003f003e004c13

def z139 : W := mkw 0x0040809031c52948 0x80040809031c5294 0x2000000011c739c8 0x02000000011c739c

def z140 : W := mkw 0x2b700f501b281e0e 0x02b700f501b281e0 0xbff00e701e381e00 0xdbff00e701e381e0

def z141 : W := mkw 0x0b700f4019200000 0x00b700f401920000 0xbff00ff01ff8000d 0xfbff00ff01ff8000

def z142 : W := mkw 0x040a90000496c000 0x0040a90000496c00 0x3e3ff0001fffc00b 0xe3e3ff0001fffc00

def z143 : W := mkw 0x164a0c9a1742bca9 0x0164a0c9a1742bca 0xffce0fff1fc7ffff 0xfffce0fff1fc7fff

def z144 : W := mkw 0x8fefdc0a1db7c000 0x08fefdc0a1db7c00 0xfffffe0f1fffc00f 0xffffffe0f1fffc00

def z145 : W := mkw 0x6fff6fffdb683e0e 0x06fff6fffdb683e0 0xfffffffffff83e0f 0xffffffffffff83e0

def z146 : W := mkw 0x448f602fc0000000 0x0448f602fc000000 0x400ff00fe0000002 0x0400ff00fe000000

def z147 : W := mkw 0x440a600b40000000 0x0440a600b4000000 0x0002700300000000 0x0000270030000000

def z148 : W := mkw 0x804090001db7c000 0x0804090001db7c00 0x300000001fffc008 0x0300000001fffc00

def z149 : W := mkw 0x0010b301409c4214 0x40010b301409c421 0x1033f60301fcc63b 0xa1033f60301fcc63

def z150 : W := mkw 0x0010038000482204 0x0001003800048220 0x5032078301fce73f 0xa5032078301fce73

def z151 : W := mkw 0x0d6a00001d228000 0x00d6a00001d22800 0xbffe00001fffc00b 0xebffe00001fffc00

def z152 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x0031f180e1f80001 0x00031f180e1f8000

def z153 : W := mkw 0x0000009020402948 0x8000000902040294 0x00000000000039c0 0x000000000000039c

def z154 : W := mkw 0x02000c0002001400 0x002000c000200140 0x3e000e001e003e0c 0xf3e000e001e003e0

def z155 : W := mkw 0x3f7a0fda1f6abeaf 0x03f7a0fda1f6abea 0xfffe0fff1fffffff 0xffffe0fff1ffffff

def z156 : W := mkw 0x69f563f5d9682a0e 0x069f563f5d9682a0 0x81f1f1f0e1f80001 0x081f1f1f0e1f8000

def z157 : W := mkw 0x00c500b4b1412948 0x800c500b4b141294 0xe1cc09fcf00339c4 0x5e1cc09fcf00339c

def z158 : W := mkw 0x0000000000000000 0x0000000000000000 0x600c080c100739ce 0x7600c080c100739c

def z159 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x703fff8ff1ffffff 0xf703fff8ff1fffff

def z160 : W := mkw 0x8d6ad0001db7c000 0x08d6ad0001db7c00 0x3e3270001fffc008 0x83e3270001fffc00

def z161 : W := mkw 0x9defd00a1db7c0a1 0x09defd00a1db7c0a 0xfffff00f1fffc1fb 0xefffff00f1fffc1f

def z162 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x4031f783e1f82735 0x04031f783e1f8273

def z163 : W := mkw 0x8dfff3817dffe314 0x48dfff3817dffe31 0xfffff783ffffe73f 0xefffff783ffffe73

def z164 : W := mkw 0xafff4fd01f6bbe0e 0x0afff4fd01f6bbe0 0xbffc0ff01ffb3e0d 0xfbffc0ff01ffb3e0

def z165 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0x4e3ff60fe0000002 0x84e3ff60fe000000

def z166 : W := mkw 0x040a000004028000 0x0040a00000402800 0x3e0e00001e07c00a 0xe3e0e00001e07c00

def z167 : W := mkw 0x008580b4a0c52948 0x8008580b4a0c5294 0x400d89fce00739c6 0x1400d89fce00739c

def z168 : W := mkw 0x22102fd162483f1e 0x422102fd162483f1 0x40000ff3e0003f34 0x140000ff3e0003f3

def z169 : W := mkw 0x12000cbea2403de9 0x812000cbea2403de 0x40000fffe0003ff4 0x140000fffe0003ff

def z170 : W := mkw 0x0000908020dc6314 0x40000908020dc631 0x1033f00001fce73b 0xa1033f00001fce73

def z171 : W := mkw 0x0000900000944000 0x0000090000094400 0x0003f0000004c002 0x00003f0000004c00

def z172 : W := mkw 0x3f7a0fda1f6abeaf 0x03f7a0fda1f6abea 0xbff20ff31ff8fe3d 0xfbff20ff31ff8fe3

def z173 : W := mkw 0xcffffffffdf7e948 0x8cffffffffdf7e94 0xfffffffffffff9cf 0xffffffffffffff9c

def z174 : W := mkw 0x0040009011402808 0x0004000901140280 0xe1cc09fc11c739cf 0x7e1cc09fc11c739c

def z175 : W := mkw 0x140a000a040280a1 0x0140a000a040280a 0x400e000f0007c1f2 0x0400e000f0007c1f

def z176 : W := mkw 0x297003d019682a0e 0x0297003d019682a0 0x81f001f001f80001 0x081f001f001f8000

def z177 : W := mkw 0x2f7a0fd01f6abe0e 0x02f7a0fd01f6abe0 0xbffe0ff01ffffe0f 0xfbffe0ff01ffffe0

def z178 : W := mkw 0x8dafd0000497c000 0x08dafd0000497c00 0x8ffff0000007c003 0xe8ffff0000007c00

def z179 : W := mkw 0x000000b4a0402948 0x8000000b4a040294 0x400009fce00039c4 0x1400009fce00039c

def z180 : W := mkw 0x00858024a0850140 0x800858024a085014 0x600d880cf00739ce 0x7600d880cf00739c

def z181 : W := mkw 0x008580a4a0c42100 0x0008580a4a0c4210 0xc1cd89fce1c4210f 0x7c1cd89fce1c4210

def z182 : W := mkw 0x0040800011850000 0x0004080001185000 0x2000000011c70008 0x02000000011c7000

def z183 : W := mkw 0x49b5f3e5e0dc6314 0x449b5f3e5e0dc631 0xd1f3f7f3e1fce73f 0xad1f3f7f3e1fce73

def z184 : W := mkw 0x160a8c8a26c6b5a1 0x0160a8c8a26c6b5a 0x7e0f8f8fffc7ffff 0xf7e0f8f8fffc7fff

def z185 : W := mkw 0x2be58cf4bbe53d4a 0x82be58cf4bbe53d4 0xefcd89fcffc739cf 0x7efcd89fcffc739c

def z186 : W := mkw 0x3f6a0c5a1f229cab 0x03f6a0c5a1f229ca 0xffce0e7f1e07fffe 0xfffce0e7f1e07fff

def z187 : W := mkw 0x8defd0b4bdf7e948 0x88defd0b4bdf7e94 0xbffff1f0ffffc00b 0xebffff1f0ffffc00

def z188 : W := mkw 0x8d6a50001d32c000 0x08d6a50001d32c00 0xbff270001ff8c009 0xebff270001ff8c00

def z189 : W := mkw 0x0010230140000000 0x0001023014000000 0x5033f783e004e73f 0xa5033f783e004e73

def z190 : W := mkw 0x000000b4a0402948 0x8000000b4a040294 0x600c09fcf00739ce 0x7600c09fcf00739c

def z191 : W := mkw 0x001023b5e0482b5c 0xc001023b5e0482b5 0x40000fffe0003ff4 0x140000fffe0003ff

def z192 : W := mkw 0x204090903bfc7f1e 0x4204090903bfc7f1 0x300000001ffcff38 0x0300000001ffcff3

def z193 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x1033f783e1f8c631 0x81033f783e1f8c63

def z194 : W := mkw 0x0000908020dc6314 0x40000908020dc631 0x5002060301fce73e 0xa5002060301fce73

def z195 : W := mkw 0x2bf5bff5fbfd7f5e 0xc2bf5bff5fbfd7f5 0xffffffffffffffff 0xffffffffffffffff

def z196 : W := mkw 0x0000200160000110 0x4000020016000011 0x40000003e0000130 0x040000003e000013

def z197 : W := mkw 0x0000900000944000 0x0000090000094400 0x1033f00001fcc00b 0xa1033f00001fcc00

def z198 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x1032760301fce738 0x81032760301fce73

def z199 : W := mkw 0x49f5e3f5f1c52948 0x849f5e3f5f1c5294 0x81f1f1f0e1c00001 0x081f1f1f0e1c0000

def z200 : W := mkw 0x0010330140184214 0x4001033014018421 0x103276030038c630 0x8103276030038c63

def z201 : W := mkw 0xc48ff02fc497c000 0x0c48ff02fc497c00 0x400ff00fe007c002 0x0400ff00fe007c00

def z202 : W := mkw 0xcfffff6fddb7c000 0x0cfffff6fddb7c00 0xffffffffffffc00f 0xfffffffffffffc00

def z203 : W := mkw 0x161a3f0b461ad6b5 0x4161a3f0b461ad6b 0x1e3276030e38c630 0x81e3276030e38c63

def z204 : W := mkw 0xcfffffeffdffe314 0x4cfffffeffdffe31 0xffffffffffffe73f 0xfffffffffffffe73

def z205 : W := mkw 0x29f583f4b9ed2b4e 0x829f583f4b9ed2b4 0x81f181f0e1f80001 0x081f181f0e1f8000

def z206 : W := mkw 0x0daf400004028000 0x00daf40000402800 0xbffff0001e07c00b 0xebffff0001e07c00

def z207 : W := mkw 0x22d58ff4b3cd3f4e 0x822d58ff4b3cd3f4 0xe1cd8ffcf1c73fcf 0x7e1cd8ffcf1c73fc

def z208 : W := mkw 0x2040009019682a0e 0x02040009019682a0 0x0000000001f80000 0x00000000001f8000

def z209 : W := mkw 0x0000100000104000 0x0000010000010400 0x103270000038c000 0x8103270000038c00

def z210 : W := mkw 0x0040001011000808 0x0004000101100080 0xa1c0087010001800 0x5a1c008701000180

def z211 : W := mkw 0x2b600c501b201c0a 0x02b600c501b201c0 0xbff008701ff81809 0xfbff008701ff8180

def z212 : W := mkw 0x49a5406480000000 0x049a540648000000 0x81c0007000000000 0x081c000700000000

def z213 : W := mkw 0x8dfff3015dbfc214 0x48dfff3015dbfc21 0xbffff6031fffc63b 0xebffff6031fffc63

def z214 : W := mkw 0xcfffff4b5db7c000 0x0cfffff4b5db7c00 0xbffff6031fffc00b 0xebffff6031fffc00

def z215 : W := mkw 0x201003d000482a0e 0x0201003d000482a0 0x000001f000000000 0x0000001f00000000

def z216 : W := mkw 0x02000c0a00000000 0x002000c0a0000000 0x40000e0f00000004 0x140000e0f0000000

def z217 : W := mkw 0x4930634140000000 0x0493063414000000 0x0030700000000000 0x0003070000000000

def z218 : W := mkw 0x204000901b683e0e 0x0204000901b683e0 0xb1c009f01ff83e0d 0x7b1c009f01ff83e0

def z219 : W := mkw 0x00c5800011850000 0x000c580001185000 0xa1cd800011c7000b 0x6a1cd800011c7000

def z220 : W := mkw 0x0f3a0f4a00000000 0x00f3a0f4a0000000 0xcffe0fff00000007 0xfcffe0fff0000000

def z221 : W := mkw 0x52102f6fc20014a1 0x052102f6fc20014a 0x40000fffe0003ff4 0x140000fffe0003ff

def z222 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcfcc0fffe0000004 0x5cfcc0fffe000000

def z223 : W := mkw 0x2be50c749b211c4a 0x82be50c749b211c4 0xafcc087c1e0318c0 0x5afcc087c1e0318c

def z224 : W := mkw 0x0bf58ff4b1c52948 0x80bf58ff4b1c5294 0xeffd8ffcf1c739cf 0xfeffd8ffcf1c739c

def z225 : W := mkw 0x8920500008304000 0x0892050000830400 0x0030700000380000 0x0003070000038000

def z226 : W := mkw 0x5f3a6f4b460294a1 0x05f3a6f4b460294a 0x7e3e7e0f1e07fffe 0xf7e3e7e0f1e07fff

def z227 : W := mkw 0x140a000a040280a1 0x0140a000a040280a 0x000c000c000300c0 0x0000c000c000300c

def z228 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xeffffffffe0318c7 0xfeffffffffe0318c

def z229 : W := mkw 0x00c5800011850000 0x000c580001185000 0x81c1800001c00001 0x081c1800001c0000

def z230 : W := mkw 0x2f7a0fda1b683e0e 0x02f7a0fda1b683e0 0xfffe0fff1ff83e0f 0xffffe0fff1ff83e0

def z231 : W := mkw 0x8defd0803df7e100 0x08defd0803df7e10 0xfffff180ffffe10f 0xefffff180ffffe10

def z232 : W := mkw 0x0040909031dd6b5c 0xc0040909031dd6b5 0x3000000011fffff8 0x03000000011fffff

def z233 : W := mkw 0x8d2a50000c32c000 0x08d2a50000c32c00 0x3e3e70001e3fc00a 0xe3e3e70001e3fc00

def z234 : W := mkw 0xdfffff6fdfb7d4a1 0x0dfffff6fdfb7d4a 0xffffffffffffffff 0xffffffffffffffff

def z235 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xdfffffffee00c637 0xfdfffffffee00c63

def z236 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0x81fff00001ffc003 0x081fff00001ffc00

def z237 : W := mkw 0xcfef4c6e9d238000 0x0cfef4c6e9d23800 0xafcc087c1e030000 0x5afcc087c1e03000

def z238 : W := mkw 0x42102f6fc0000000 0x042102f6fc000000 0x40000fffe0000004 0x140000fffe000000

def z239 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0x8ffe7e7f00000000 0xd8ffe7e7f0000000

def z240 : W := mkw 0x040a000004028000 0x0040a00000402800 0x7e0e06031e07e73e 0xe7e0e06031e07e73

def z241 : W := mkw 0x22100ff4a2483f4e 0x822100ff4a2483f4 0x40000ffce0003fc4 0x140000ffce0003fc

def z242 : W := mkw 0x22100fd002483e0e 0x022100fd002483e0 0x3e000ff01e003e0c 0xf3e000ff01e003e0

def z243 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000000004e738 0x0100000000004e73

def z244 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x3e0206031e07fff8 0x83e0206031e07fff

def z245 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xa1c189f0f1c0380d 0x7a1c189f0f1c0380

def z246 : W := mkw 0x0fbf4f4000000000 0x00fbf4f400000000 0x8ffffff000000007 0xf8ffffff00000000

def z247 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xaff009f01ff81801 0x5aff009f01ff8180

def z248 : W := mkw 0x200000000a281606 0x0200000000a28160 0x100000000e380600 0x0100000000e38060

def z249 : W := mkw 0x4fbf6f4b40000000 0x04fbf6f4b4000000 0x8ffff60300000003 0xe8ffff6030000000

def z250 : W := mkw 0x0085002480000000 0x0008500248000000 0xe1cd89fcf00739cf 0x7e1cd89fcf00739c

def z251 : W := mkw 0x2b700fd019682a0e 0x02b700fd019682a0 0x8ff00ff001f80005 0xf8ff00ff001f8000

def z252 : W := mkw 0x004080b4b1c52948 0x8004080b4b1c5294 0x600009fcf1c739cc 0x1600009fcf1c739c

def z253 : W := mkw 0x964a9c0a1fb7d4a1 0x0964a9c0a1fb7d4a 0x7e0e0e0f1ffffffe 0xf7e0e0e0f1ffffff

def z254 : W := mkw 0x00c5808031c52100 0x000c5808031c5210 0xe1cd8180f1c7210f 0x6e1cd8180f1c7210

def z255 : W := mkw 0x0000908020dc6314 0x40000908020dc631 0x0000000001f80000 0x00000000001f8000

def z256 : W := mkw 0x5fbf6f6fc40280a1 0x05fbf6f6fc40280a 0xcfffffffe007c1f7 0xfcfffffffe007c1f

def z257 : W := mkw 0x4fbf4f6e80000000 0x04fbf4f6e8000000 0x8ffc0ffc00000005 0xf8ffc0ffc0000000

def z258 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000100739c8 0x020000000100739c

def z259 : W := mkw 0x0040009011402808 0x0004000901140280 0x2000000011c03808 0x02000000011c0380

def z260 : W := mkw 0x8d2ad0000cb6c000 0x08d2ad0000cb6c00 0x1e33f0000ffcc00b 0xa1e33f0000ffcc00

def z261 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x6e0e080f1e07d9f2 0x56e0e080f1e07d9f

def z262 : W := mkw 0x2b300f400a281606 0x02b300f400a28160 0x1e3006000e380600 0x81e3006000e38060

def z263 : W := mkw 0x00d5b3b5f1dd6b5c 0xc00d5b3b5f1dd6b5 0xe1fdf9fcf1ff39cf 0x7e1fdf9fcf1ff39c

def z264 : W := mkw 0x6ffffffffbfc7f1e 0x46ffffffffbfc7f1 0xfffffffffffcff3f 0xffffffffffffcff3

def z265 : W := mkw 0x2fff4fd01b683e0e 0x02fff4fd01b683e0 0xbffffff01ff83e0f 0xfbffffff01ff83e0

def z266 : W := mkw 0x0010238160482314 0x4001023816048231 0x40000783e0002734 0x040000783e000273

def z267 : W := mkw 0x0000908020d46100 0x00000908020d4610 0x5033f180e1fce10f 0xa5033f180e1fce10

def z268 : W := mkw 0x2000009002483e0e 0x02000009002483e0 0x0000000000003e00 0x00000000000003e0

def z269 : W := mkw 0x0010238160482314 0x4001023816048231 0x50300783e1f8273d 0xa50300783e1f8273

def z270 : W := mkw 0xcf3a7f4b4c32c000 0x0cf3a7f4b4c32c00 0x1e3276030e38c000 0x81e3276030e38c00

def z271 : W := mkw 0x0daf400000000000 0x00daf40000000000 0x8ffff00000000003 0xe8ffff0000000000

def z272 : W := mkw 0x8defc0b4bde7a948 0x88defc0b4bde7a94 0xefcd89fcffc739cf 0x7efcd89fcffc739c

def z273 : W := mkw 0x9fef4c0a1f2394a1 0x09fef4c0a1f2394a 0xffce0e0f1e07fffe 0xfffce0e0f1e07fff

def z274 : W := mkw 0x040a000004028000 0x0040a00000402800 0x1e0200000e00c000 0x81e0200000e00c00

def z275 : W := mkw 0x5f3a6f4b460294a1 0x05f3a6f4b460294a 0x1e3276030e00c630 0x81e3276030e00c63

def z276 : W := mkw 0x02400c9013403c08 0x002400c9013403c0 0xbfc00ff01fc03e0d 0xfbfc00ff01fc03e0

def z277 : W := mkw 0x80c590001db7c000 0x080c590001db7c00 0xb1cd80001fffc00b 0x6b1cd80001fffc00

def z278 : W := mkw 0x0000000000000000 0x0000000000000000 0x100200000004c00a 0xa100200000004c00

def z279 : W := mkw 0x12000c0a020014a1 0x012000c0a020014a 0x50020e0f0004fffe 0xb50020e0f0004fff

def z280 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xeffffffff00739cf 0xfeffffffff00739c

def z281 : W := mkw 0x297003d019682a0e 0x0297003d019682a0 0xa1f009f011f8380d 0x7a1f009f011f8380

def z282 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xaffdf0001ffb0001 0x4affdf0001ffb000

def z283 : W := mkw 0x1000908026def7b5 0x41000908026def7b 0x300000001ffffff8 0x0300000001ffffff

def z284 : W := mkw 0x848ff0016497c110 0x4848ff0016497c11 0x400ff003e007c132 0x0400ff003e007c13

def z285 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0x9ff007f00ff80601 0x89ff007f00ff8060

def z286 : W := mkw 0x5fbfffefe6def7b5 0x45fbfffefe6def7b 0xffffffffffffffff 0xffffffffffffffff

def z287 : W := mkw 0x561a2f6fc60294a1 0x0561a2f6fc60294a 0x7e0e0ffffe07fffe 0xf7e0e0ffffe07fff

def z288 : W := mkw 0x16cf0c3e97039ce9 0x816cf0c3e97039ce 0xffce0e7f1e07fffe 0xfffce0e7f1e07fff

def z289 : W := mkw 0x848fd0000497c000 0x0848fd0000497c00 0x103ff00001ffc00b 0xa103ff00001ffc00

def z290 : W := mkw 0x42102f4b40000000 0x042102f4b4000000 0x0000060300000000 0x0000006030000000

def z291 : W := mkw 0x62102fffc2483e0e 0x062102fffc2483e0 0x40000fffe0003e04 0x140000fffe0003e0

def z292 : W := mkw 0x44cfe0bff1c52948 0x844cfe0bff1c5294 0xe1cff9fff1c739cf 0x7e1cff9fff1c739c

def z293 : W := mkw 0x42102f6fc0000000 0x042102f6fc000000 0x4033ffffe0000007 0xb4033ffffe000000

def z294 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x3e020e031e00fe3c 0xf3e020e031e00fe3

def z295 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x3e0e06031e07c63a 0xe3e0e06031e07c63

def z296 : W := mkw 0x12000c0a020014a1 0x012000c0a020014a 0x600c0e0f10073ffe 0x7600c0e0f10073ff

def z297 : W := mkw 0x448f602fc0000000 0x0448f602fc000000 0xc1cff9ffe0000007 0x7c1cff9ffe000000

def z298 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xc1c189fce1c039c5 0x1c1c189fce1c039c

def z299 : W := mkw 0x449ff3afe0dc6314 0x4449ff3afe0dc631 0x503ff78fe1fce73f 0xa503ff78fe1fce73

def z300 : W := mkw 0x0dbf630140000000 0x00dbf63014000000 0xcffff783e0000007 0xecffff783e000000

def z301 : W := mkw 0x0095b3a5e0dd6354 0xc0095b3a5e0dd635 0x503ff78fe1ffe7ff 0xa503ff78fe1ffe7f

def z302 : W := mkw 0x7fff6fffdf6abeaf 0x07fff6fffdf6abea 0xffffffffffffffff 0xffffffffffffffff

def z303 : W := mkw 0x6fff6f7fdb201c0a 0x06fff6f7fdb201c0 0xeffffffffe001807 0xfeffffffffe00180

def z304 : W := mkw 0x8defd0901df7e808 0x08defd0901df7e80 0xbffff9f01ffff80f 0xfbffff9f01ffff80

def z305 : W := mkw 0x060a0c0a00000000 0x0060a0c0a0000000 0x6e0e0e0f100739ce 0xf6e0e0e0f100739c

def z306 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x6e0c080c1e0739ce 0x76e0c080c1e0739c

def z307 : W := mkw 0x2b300f400a281606 0x02b300f400a28160 0x9ff00ff00e380605 0xf9ff00ff00e38060

def z308 : W := mkw 0x2930034008280206 0x0293003400828020 0x0030000000380000 0x0003000000038000

def z309 : W := mkw 0x00c5003491010848 0x800c500349101084 0xe1cd89fcf00318c7 0x7e1cd89fcf00318c

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x400c000c000701c2 0x0400c000c000701c

def z311 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0x3e3006001ff83e08 0x83e3006001ff83e0

def z312 : W := mkw 0x02000c0000000000 0x002000c000000000 0x0e000e0000000004 0xf0e000e000000000

def z313 : W := mkw 0x0000800020840100 0x0000080002084010 0x40018000e0040102 0x040018000e004010

def z314 : W := mkw 0x0000200140000000 0x0000020014000000 0x4003f003e0000002 0x04003f003e000000

def z315 : W := mkw 0xcfff6f6fdd238000 0x0cfff6f6fdd23800 0xeffffffffe030007 0xfeffffffffe03000

def z316 : W := mkw 0x840a50000412c000 0x0840a50000412c00 0x000270000000c000 0x0000270000000c00

def z317 : W := mkw 0x2b300fd00a683e0e 0x02b300fd00a683e0 0x1e300ff00e383e04 0x91e300ff00e383e0

def z318 : W := mkw 0x00c5802491850000 0x000c580249185000 0xe1cd89fcf1c7000f 0x7e1cd89fcf1c7000

def z319 : W := mkw 0x4fbf6fefc0482204 0x04fbf6fefc048220 0xdfffffffe1f8260f 0xfdfffffffe1f8260

def z320 : W := mkw 0x448f402e80000000 0x0448f402e8000000 0x000c000c00000000 0x0000c000c0000000

def z321 : W := mkw 0x2b709fd01bfc7e0e 0x02b709fd01bfc7e0 0xbff3fff01ffcfe0f 0xfbff3fff01ffcfe0

def z322 : W := mkw 0x0b600c001b201400 0x00b600c001b20140 0xbff00e001ff83e0d 0xfbff00e001ff83e0

def z323 : W := mkw 0xefffffffdffffe0e 0x0efffffffdffffe0 0xfffffffffffffe0f 0xffffffffffffffe0

def z324 : W := mkw 0x800090000497c000 0x0800090000497c00 0x000000000007c000 0x0000000000007c00

def z325 : W := mkw 0x204000101b201c0a 0x0204000101b201c0 0x200000001e001800 0x0200000001e00180

def z326 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x6e0e0e0f1e0318c6 0xf6e0e0e0f1e0318c

def z327 : W := mkw 0x6fff4ffe9b683e0e 0x06fff4ffe9b683e0 0xbffc0ffc1ff83e0d 0xfbffc0ffc1ff83e0

def z328 : W := mkw 0x3b700fda1b683eaf 0x03b700fda1b683ea 0xfff00fff1ff83ffd 0xffff00fff1ff83ff

def z329 : W := mkw 0x2b300f400a281606 0x02b300f400a28160 0x3e300e001e383e0c 0xf3e300e001e383e0

def z330 : W := mkw 0xa9f5d3d019fd6a0e 0x0a9f5d3d019fd6a0 0x81f1f1f001f80001 0x081f1f1f001f8000

def z331 : W := mkw 0x12000c0a060294a1 0x012000c0a060294a 0x70000e0f1e07fffc 0x170000e0f1e07fff

def z332 : W := mkw 0x02000c0002001400 0x002000c000200140 0x7e020e031e04ff3e 0xf7e020e031e04ff3

def z333 : W := mkw 0x161abf8b66def7b5 0x4161abf8b66def7b 0x5e33f783effce73f 0xa5e33f783effce73

def z334 : W := mkw 0xcdfff365ddb7c000 0x0cdfff365ddb7c00 0xbffff1f0ffffc00b 0xebffff1f0ffffc00

def z335 : W := mkw 0xab709fd01ffffe0e 0x0ab709fd01ffffe0 0xbff00ff01ffffe0d 0xfbff00ff01ffffe0

def z336 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xafcff0001e07c002 0x4afcff0001e07c00

def z337 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x1031f180e1fce739 0x01031f180e1fce73

def z338 : W := mkw 0x0040809031c52948 0x80040809031c5294 0x0000000001c00000 0x00000000001c0000

def z339 : W := mkw 0x00c5809011c52808 0x000c5809011c5280 0xa1cd89f011c7380f 0x7a1cd89f011c7380

def z340 : W := mkw 0x848f400004038000 0x0848f40000403800 0x000c000000030000 0x0000c00000003000

def z341 : W := mkw 0x0d2a400000000000 0x00d2a40000000000 0x0e32700000000000 0x80e3270000000000

def z342 : W := mkw 0x4faf4c6e80000000 0x04faf4c6e8000000 0xcfce0e7f00000006 0xfcfce0e7f0000000

def z343 : W := mkw 0x6f7a6fdb5b683e0e 0x06f7a6fdb5b683e0 0xbff27ff31ff83e0d 0xfbff27ff31ff83e0

def z344 : W := mkw 0x49f5e3f5f1c52948 0x849f5e3f5f1c5294 0xe1fdf9fcf1c739cf 0x7e1fdf9fcf1c739c

def z345 : W := mkw 0x4f3a6f4b40000000 0x04f3a6f4b4000000 0x4e3e7e0f00000006 0xf4e3e7e0f0000000

def z346 : W := mkw 0x0b30bfc160dc6314 0x40b30bfc160dc631 0xdff3fff3e1fce73f 0xfdff3fff3e1fce73

def z347 : W := mkw 0x0daf402480000000 0x00daf40248000000 0xcffff9fce0000007 0xfcffff9fce000000

def z348 : W := mkw 0x048f400000000000 0x0048f40000000000 0x000ff00000000002 0x0000ff0000000000

def z349 : W := mkw 0x8def50001d33c000 0x08def50001d33c00 0xbffe70001e3bc000 0xcbffe70001e3bc00

def z350 : W := mkw 0x0085b025e0954150 0xc0085b025e095415 0x400ff00fe007c1f2 0x0400ff00fe007c1f

def z351 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c00001007000a 0x6200c00001007000

def z352 : W := mkw 0x10000000020014a1 0x010000000020014a 0x0000000000003ff0 0x00000000000003ff

def z353 : W := mkw 0x1210bf8b62dc77b5 0x41210bf8b62dc77b 0x5033ff8fe1fcffff 0xb5033ff8fe1fcfff

def z354 : W := mkw 0x0010230140080214 0x4001023014008021 0x0000060300000630 0x0000006030000063

def z355 : W := mkw 0x0085002480010040 0x8008500248001004 0x000c000c000300c0 0x0000c000c000300c

def z356 : W := mkw 0xafefdc501fb7dc0a 0x0afefdc501fb7dc0 0xbffff8701fffd80b 0xfbffff8701fffd80

def z357 : W := mkw 0x0b700fd011402808 0x00b700fd01140280 0xaff00ff011c0380d 0xfaff00ff011c0380

def z358 : W := mkw 0x4fbf6f6fc2001400 0x04fbf6f6fc200140 0xfffffffffe003e0f 0xffffffffffe003e0

def z359 : W := mkw 0x09a5400000000000 0x009a540000000000 0x81f1f00000000001 0x081f1f0000000000

def z360 : W := mkw 0x12000c0a020014a1 0x012000c0a020014a 0x7e000e0f1e003ffc 0xf7e000e0f1e003ff

def z361 : W := mkw 0x8def40001d238000 0x08def40001d23800 0xaffff0001e030003 0xeaffff0001e03000

def z362 : W := mkw 0x10000000060294a1 0x010000000060294a 0x700206031e07fffe 0xa700206031e07fff

def z363 : W := mkw 0x4f3affcb60dc6314 0x44f3affcb60dc631 0x5e33f783e1fce73f 0xa5e33f783e1fce73

def z364 : W := mkw 0x8d3af3816cfee314 0x48d3af3816cfee31 0x5e33f783effce73f 0xa5e33f783effce73

def z365 : W := mkw 0x89e5d0b4b9f56948 0x889e5d0b4b9f5694 0xe1fdf9fcf1ff39cf 0x7e1fdf9fcf1ff39c

def z366 : W := mkw 0x02100f4000000000 0x002100f400000000 0x00000ff000000004 0x100000ff00000000

def z367 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0x8ffdf9fce0000001 0x58ffdf9fce000000

def z368 : W := mkw 0x2bf58ff4bbed3f4e 0x82bf58ff4bbed3f4 0xfffd8ffcffff3fcf 0xffffd8ffcffff3fc

def z369 : W := mkw 0x060a0c0a00000000 0x0060a0c0a0000000 0x0e0c080c00000000 0x50e0c080c0000000

def z370 : W := mkw 0xbfffdfda1ffffeaf 0x0bfffdfda1ffffea 0xffffffff1fffffff 0xfffffffff1ffffff

def z371 : W := mkw 0x8085d00000954000 0x08085d0000095400 0x0001f00000000000 0x00001f0000000000

def z372 : W := mkw 0x040a000004028000 0x0040a00000402800 0x000e00000007c002 0x0000e00000007c00

def z373 : W := mkw 0x00c5900011954000 0x000c590001195400 0xb1fff00011ffc00b 0xeb1fff00011ffc00

def z374 : W := mkw 0x0000008020482314 0x4000000802048231 0x0000000000002730 0x0000000000000273

def z375 : W := mkw 0x848fd0000497c000 0x0848fd0000497c00 0x3e0ff0001e07c00a 0xe3e0ff0001e07c00

def z376 : W := mkw 0x22500fd01b683e0e 0x022500fd01b683e0 0x30000ff01ff83e0c 0x130000ff01ff83e0

def z377 : W := mkw 0x060a0c0a04028000 0x0060a0c0a0402800 0x7e0e0e0f1e07c00e 0xf7e0e0e0f1e07c00

def z378 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0x9ff3f0000ff8c001 0x89ff3f0000ff8c00

def z379 : W := mkw 0x548f602fc40280a1 0x0548f602fc40280a 0x400ff00fe007c1f2 0x0400ff00fe007c1f

def z380 : W := mkw 0x00c500b491402808 0x000c500b49140280 0xe1cd89fcf1c0380f 0x7e1cd89fcf1c0380

def z381 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c080c100318c0 0x5200c080c100318c

def z382 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xdfffffffe004e73f 0xfdfffffffe004e73

def z383 : W := mkw 0x296000501920080a 0x0296000501920080 0x81c0007000000000 0x081c000700000000

def z384 : W := mkw 0x8040900019b54000 0x08040900019b5400 0x0000000001f80000 0x00000000001f8000

def z385 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x4033f783e1f80007 0xa4033f783e1f8000

def z386 : W := mkw 0x00d5b3b5f1dd6b5c 0xc00d5b3b5f1dd6b5 0xd1f3f7f3e1fce73f 0xad1f3f7f3e1fce73

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x81c009f000000005 0x781c009f00000000

def z388 : W := mkw 0x8defd0903df7e948 0x88defd0903df7e94 0xbffff0001ffff9cb 0xebffff0001ffff9c

def z389 : W := mkw 0x14cf80beb5c7a9e9 0x814cf80beb5c7a9e 0xe1cf89fff1c7f9ff 0x7e1cf89fff1c7f9f

def z390 : W := mkw 0x4f2a4c4a00000000 0x04f2a4c4a0000000 0x0e00000000000000 0x00e0000000000000

def z391 : W := mkw 0x3f7abfdb7ffeffbf 0x43f7abfdb7ffeffb 0xffffffffffffffff 0xffffffffffffffff

def z392 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xa1cd81f0f1c7000b 0x6a1cd81f0f1c7000

def z393 : W := mkw 0x2b70bfd17bfc7f1e 0x42b70bfd17bfc7f1 0xbff1fff0fff83e0d 0xfbff1fff0fff83e0

def z394 : W := mkw 0x8defd0249db7c000 0x08defd0249db7c00 0xfffff9fcffffc00f 0xffffff9fcffffc00

def z395 : W := mkw 0x00c5800011850000 0x000c580001185000 0xe1cd880c11c739cf 0x7e1cd880c11c739c

def z396 : W := mkw 0x4dbf636fc0000000 0x04dbf636fc000000 0xc1fff1ffe0000003 0x0c1fff1ffe000000

def z397 : W := mkw 0x948fd00a0497c0a1 0x0948fd00a0497c0a 0x400ff00f0007c1f2 0x0400ff00f0007c1f

def z398 : W := mkw 0x2b600c501b201c0a 0x02b600c501b201c0 0xbfc00e701e003e0c 0xfbfc00e701e003e0

def z399 : W := mkw 0x5fffeffff7c7bde9 0x85fffeffff7c7bde 0xffffffffffc7ffff 0xfffffffffffc7fff

def z400 : W := mkw 0x42d5affff1c52948 0x842d5affff1c5294 0xe1cd8ffff1c739cf 0x7e1cd8ffff1c739c

def z401 : W := mkw 0x8defd0803dffe314 0x48defd0803dffe31 0xbffff0001fffe73b 0xebffff0001fffe73

def z402 : W := mkw 0x0210bf8162dc7714 0x40210bf8162dc771 0x7e33ff83fffcff3f 0xf7e33ff83fffcff3

def z403 : W := mkw 0x0010a38160cc2314 0x40010a38160cc231 0x40018783e1c4273f 0x240018783e1c4273

def z404 : W := mkw 0x3f6a0c5a1f229cab 0x03f6a0c5a1f229ca 0xafcc087c1e0318c0 0x5afcc087c1e0318c

def z405 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xa1c181f0f1c739c9 0x0a1c181f0f1c739c

def z406 : W := mkw 0x040a000000000000 0x0040a00000000000 0x0e0e000000000002 0xe0e0e00000000000

def z407 : W := mkw 0x2b708fd03bed3f4e 0x82b708fd03bed3f4 0xbff00ff01fff3fcd 0xfbff00ff01fff3fc

def z408 : W := mkw 0x0000100000184214 0x4000010000018421 0x100000000038c630 0x0100000000038c63

def z409 : W := mkw 0x205003901b683e0e 0x0205003901b683e0 0x303007801ff83e0d 0xa303007801ff83e0

def z410 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x5e0206030e04e73e 0xa5e0206030e04e73

def z411 : W := mkw 0x2b709fd03bfc7f1e 0x42b709fd03bfc7f1 0xbff00ff01ffcff3d 0xfbff00ff01ffcff3

def z412 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xfffff80c1ffff9cf 0xffffff80c1ffff9c

def z413 : W := mkw 0x1f6a0c0a1f2294a1 0x01f6a0c0a1f2294a 0xfffe0e0f1fffffff 0xffffe0e0f1ffffff

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0x40018180e0000007 0x240018180e000000

def z415 : W := mkw 0x6fbf6f6fca281606 0x06fbf6f6fca28160 0xdfffffffee380607 0xfdfffffffee38060

def z416 : W := mkw 0x8fefdc001fb7d400 0x08fefdc001fb7d40 0xbffffe001ffffe0f 0xfbffffe001ffffe0

def z417 : W := mkw 0x0920000000000000 0x0092000000000000 0x8ff0000000000001 0xe8ff000000000000

def z418 : W := mkw 0x0010938000dc6204 0x00010938000dc620 0x1033f78001fce60f 0xa1033f78001fce60

def z419 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000000004210e 0x2400000000004210

def z420 : W := mkw 0x22100fd002483e0e 0x022100fd002483e0 0x10300ff001f83e0d 0xb10300ff001f83e0

def z421 : W := mkw 0x16cf0c3e97039ce9 0x816cf0c3e97039ce 0xafcc087c1e0318c0 0x5afcc087c1e0318c

def z422 : W := mkw 0x0010b301609c4314 0x40010b301609c431 0x5033f603e03cc732 0x85033f603e03cc73

def z423 : W := mkw 0x84cfd0001db7c000 0x084cfd0001db7c00 0x300ff0001fffc00a 0x0300ff0001fffc00

def z424 : W := mkw 0x00c5b0b5f1d56958 0xc00c5b0b5f1d5695 0xe1cff9fff1c7f9ff 0x7e1cff9fff1c7f9f

def z425 : W := mkw 0x89e5d00019b54000 0x089e5d00019b5400 0xa1fdf00011ff000b 0x6a1fdf00011ff000

def z426 : W := mkw 0xcfffff6fd9b54000 0x0cfffff6fd9b5400 0xcfffffffe1f80007 0xfcfffffffe1f8000

def z427 : W := mkw 0x140a000a060294a1 0x0140a000a060294a 0x700e000f1e07fffa 0x0700e000f1e07fff

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0x100006000000260c 0xa100006000000260

def z429 : W := mkw 0x0000808020c42100 0x00000808020c4210 0x600d898cf1c739cf 0x7600d898cf1c739c

def z430 : W := mkw 0x068f0c2e80000000 0x0068f0c2e8000000 0xcfcf8fffe0000007 0xfcfcf8fffe000000

def z431 : W := mkw 0x00000024a0000140 0x800000024a000014 0x4000000ce00001c0 0x04000000ce00001c

def z432 : W := mkw 0xaf7a5fd01f7afe0e 0x0af7a5fd01f7afe0 0xbff27ff01ff8fe0d 0xfbff27ff01ff8fe0

def z433 : W := mkw 0x89e5d0b4b9f56948 0x889e5d0b4b9f5694 0x81f1f1f0e1f80001 0x081f1f1f0e1f8000

def z434 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xc1cd81fce1c701c3 0x0c1cd81fce1c701c

def z435 : W := mkw 0x9defd0001fb7d4a1 0x09defd0001fb7d4a 0xbffff0001ffffffb 0xebffff0001ffffff

def z436 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xafc00ff01e003e04 0x5afc00ff01e003e0

def z437 : W := mkw 0x10000000060294a1 0x010000000060294a 0x100000000e00c630 0x0100000000e00c63

def z438 : W := mkw 0x8daf50000c32c000 0x08daf50000c32c00 0x9ffff0000e38c003 0xe9ffff0000e38c00

def z439 : W := mkw 0x2b300fc00a683606 0x02b300fc00a68360 0x1e3007800ff8260d 0xa1e3007800ff8260

def z440 : W := mkw 0x9fefdc0a1fb7d4a1 0x09fefdc0a1fb7d4a 0xbffff80c1fffd8cb 0xfbffff80c1fffd8c

def z441 : W := mkw 0x09e5800019a50000 0x009e5800019a5000 0xbffd80001fff000b 0xebffd80001fff000

def z442 : W := mkw 0x0010230140000000 0x0001023014000000 0x40000783e0000004 0x040000783e000000

def z443 : W := mkw 0x00c58024b1850140 0x800c58024b185014 0xe1cd800cf1c701cb 0x6e1cd800cf1c701c

def z444 : W := mkw 0x84cfd0b4b5d7e948 0x884cfd0b4b5d7e94 0xe1cff9fcf1c7f9cf 0x7e1cff9fcf1c7f9c

def z445 : W := mkw 0x1010b38166def7b5 0x41010b38166def7b 0x7033f783ffffffff 0xa7033f783fffffff

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000080c000039c4 0x14000080c000039c

def z447 : W := mkw 0x0050b39171dd6b5c 0xc0050b39171dd6b5 0x7033f783f1ffffff 0xa7033f783f1fffff

def z448 : W := mkw 0x060a0c0a02001400 0x0060a0c0a0200140 0x7e0e0e0f1e003e0e 0xf7e0e0e0f1e003e0

def z449 : W := mkw 0x0000b00160944110 0x40000b0016094411 0x0001f000e0000000 0x00001f000e000000

def z450 : W := mkw 0x0000008020402100 0x0000000802040210 0x40000180e0002104 0x040000180e000210

def z451 : W := mkw 0x2b703fd15b787e1e 0x42b703fd15b787e1 0xbff27ff31ff8fe3d 0xfbff27ff31ff8fe3

def z452 : W := mkw 0x040a000004028000 0x0040a00000402800 0x2e0c00001e030000 0x42e0c00001e03000

def z453 : W := mkw 0x8defd00019b54000 0x08defd00019b5400 0x8ffff00001f80003 0xe8ffff00001f8000

def z454 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xfff20ff31ffcff3f 0xffff20ff31ffcff3

def z455 : W := mkw 0x804090803dffe314 0x4804090803dffe31 0x300000001fffe738 0x0300000001fffe73

def z456 : W := mkw 0x0085000000000000 0x0008500000000000 0x81cd800000000003 0x681cd80000000000

def z457 : W := mkw 0x0010330140184214 0x4001033014018421 0x0030700000380000 0x0003070000038000

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0x700e0e0f1007fffe 0xf700e0e0f1007fff

def z459 : W := mkw 0x0000908020dc6314 0x40000908020dc631 0x50018180e1fce73f 0x250018180e1fce73

def z460 : W := mkw 0x2b700f401b281606 0x02b700f401b28160 0xbff006001ff80609 0xebff006001ff8060

def z461 : W := mkw 0x00c5809031c52948 0x800c5809031c5294 0xa1cd800011c739cb 0x6a1cd800011c739c

def z462 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x3e0c080c1e07fff8 0x53e0c080c1e07fff

def z463 : W := mkw 0x844a90001db7c000 0x0844a90001db7c00 0x3e0e00001fffc00a 0xe3e0e00001fffc00

def z464 : W := mkw 0x42952f6fc0000000 0x042952f6fc000000 0xc1cd8fffe0000007 0x7c1cd8fffe000000

def z465 : W := mkw 0x0b200c4000000000 0x00b200c400000000 0x8fc0087000000000 0x58fc008700000000

def z466 : W := mkw 0x0000900000944000 0x0000090000094400 0x0031f00001f80001 0x00031f00001f8000

def z467 : W := mkw 0x297003d019682a0e 0x0297003d019682a0 0x91f007f001f8260d 0xa91f007f001f8260

def z468 : W := mkw 0x8deff0017db7c110 0x48deff0017db7c11 0xfffff003ffffc13b 0xefffff003ffffc13

def z469 : W := mkw 0x3f3a0f4a0e2a96a7 0x03f3a0f4a0e2a96a 0x1e3206030e38c630 0x81e3206030e38c63

def z470 : W := mkw 0x297003d01b683e0e 0x0297003d01b683e0 0xb1f001f01ff83e09 0x0b1f001f01ff83e0

def z471 : W := mkw 0x2b303f414a385616 0x42b303f414a38561 0x1e3276030e38c630 0x81e3276030e38c63

def z472 : W := mkw 0x0930034000000000 0x0093003400000000 0x81f001f000000001 0x081f001f00000000

def z473 : W := mkw 0x2bf58fd01bed3e0e 0x02bf58fd01bed3e0 0xbffd8ff01fff3e0f 0xfbffd8ff01fff3e0

def z474 : W := mkw 0x09e580b4b9e52948 0x809e580b4b9e5294 0xfffd89fcffff39cf 0xffffd89fcffff39c

def z475 : W := mkw 0x6fbf6fffc2483e0e 0x06fbf6fffc2483e0 0xcfffffffe0003e07 0xfcfffffffe0003e0

def z476 : W := mkw 0x0dbff38160dc6314 0x40dbff38160dc631 0xdffff783e1fce73f 0xedffff783e1fce73

def z477 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x50000783e1fce73c 0x050000783e1fce73

def z478 : W := mkw 0x2b600cd01b603c0a 0x02b600cd01b603c0 0xafc009f01fc0380d 0x7afc009f01fc0380

def z479 : W := mkw 0x2b300fd002483e0e 0x02b300fd002483e0 0x8ff00ff000003e05 0xf8ff00ff000003e0

def z480 : W := mkw 0x12000c0a020014a1 0x012000c0a020014a 0x0000080c000018c0 0x10000080c000018c

def z481 : W := mkw 0x8fffdf401db7c000 0x08fffdf401db7c00 0xbffffff01fffc00f 0xfbffffff01fffc00

def z482 : W := mkw 0x0010030000080204 0x0001003000008020 0x1030060000380600 0x8103006000038060

def z483 : W := mkw 0x804000001d238000 0x0804000001d23800 0x200000001e030000 0x0200000001e03000

def z484 : W := mkw 0x4fbf6fefe0482314 0x44fbf6fefe048231 0xcfffffffe0002737 0xfcfffffffe000273

def z485 : W := mkw 0xafffffd17fffff1e 0x4afffffd17fffff1 0xfffffff3ffffff3f 0xffffffff3ffffff3

def z486 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbfcc00001fffc008 0x4bfcc00001fffc00

def z487 : W := mkw 0x164a8c9a37c7bde9 0x8164a8c9a37c7bde 0x7e0e0e0f1fc7fffe 0xf7e0e0e0f1fc7fff

def z488 : W := mkw 0x22000c5002001c0a 0x022000c5002001c0 0x0000087000001800 0x1000008700000180

def z489 : W := mkw 0x0b300f4000000000 0x00b300f400000000 0x0e30060000000000 0x80e3006000000000

def z490 : W := mkw 0x2b700ff4bb683f4e 0x82b700ff4bb683f4 0xfff00ffcfff83fcd 0xffff00ffcfff83fc

def z491 : W := mkw 0x904090001fb7d4a1 0x0904090001fb7d4a 0x300000001ffffff8 0x0300000001ffffff

def z492 : W := mkw 0x0970b38179fc6314 0x40970b38179fc631 0xfff3f783fffce73f 0xefff3f783fffce73

def z493 : W := mkw 0x0010238160482314 0x4001023816048231 0x4033f783e0002737 0xa4033f783e000273

def z494 : W := mkw 0x0000003480000848 0x8000000348000084 0x0000087c000018c0 0x10000087c000018c

def z495 : W := mkw 0x2b702fd17b683f1e 0x42b702fd17b683f1 0xfff00ff3fff83f3d 0xffff00ff3fff83f3

def z496 : W := mkw 0x0000000000000000 0x0000000000000000 0x200008001000380c 0x7200008001000380

def z497 : W := mkw 0x16dfbfbff7dffffd 0xc16dfbfbff7dffff 0xffffffffffffffff 0xffffffffffffffff

def z498 : W := mkw 0x8defc0001da78000 0x08defc0001da7800 0xafcd80001fc7000b 0x6afcd80001fc7000

def z499 : W := mkw 0x84cfd0001597c000 0x084cfd0001597c00 0xa1cff00011c7c00b 0x6a1cff00011c7c00

def z500 : W := mkw 0x000000b4a0402948 0x8000000b4a040294 0x000001f0e0000000 0x0000001f0e000000

def z501 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x4031f180e1fc210f 0x24031f180e1fc210

def z502 : W := mkw 0x204080903bed3f4e 0x8204080903bed3f4 0x300000001fff3fc8 0x0300000001fff3fc

def z503 : W := mkw 0xadefd0901ffffe0e 0x0adefd0901ffffe0 0xbffff0001ffffe0b 0xebffff0001ffffe0

def z504 : W := mkw 0x140a0000060294a1 0x0140a0000060294a 0x3e0e00001e07fffa 0xe3e0e00001e07fff

def z505 : W := mkw 0x2b200c400a201402 0x02b200c400a20140 0x0e0000000e000000 0x00e0000000e00000

def z506 : W := mkw 0x00c5003491010848 0x800c500349101084 0x81c0007000000000 0x081c000700000000

def z507 : W := mkw 0x160a0cbea642bde9 0x8160a0cbea642bde 0x7e0e0ffffe07fffe 0xf7e0e0ffffe07fff

def z508 : W := mkw 0x02000c0002001400 0x002000c000200140 0x00000e0000003e04 0x100000e0000003e0

def z509 : W := mkw 0x3b700fd01f6abeaf 0x03b700fd01f6abea 0xbff00ff01ffffffd 0xfbff00ff01ffffff

def z510 : W := mkw 0x160a0c0a040280a1 0x0160a0c0a040280a 0x4e0e0e0f0007c1f6 0xf4e0e0e0f0007c1f

def z511 : W := mkw 0x0040000019200000 0x0004000001920000 0x300000001ff80008 0x0300000001ff8000

def z512 : W := mkw 0x896090001db7c000 0x0896090001db7c00 0xbff000001fffc009 0xebff000001fffc00

def z513 : W := mkw 0x0040001011010848 0x8004000101101084 0x20000000100318c0 0x020000000100318c

def z514 : W := mkw 0x008500b4a0402948 0x8008500b4a040294 0xc1cd89fce00039c7 0x7c1cd89fce00039c

def z515 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xfffc0ffc1fff3fcf 0xffffc0ffc1fff3fc

def z516 : W := mkw 0x364a0c9a1f6abeaf 0x0364a0c9a1f6abea 0x7e0e0e0f1ffffffe 0xf7e0e0e0f1ffffff

def z517 : W := mkw 0x0040809031c42908 0x00040809031c4290 0xe1c189f0f1c4390f 0x7e1c189f0f1c4390

def z518 : W := mkw 0x00858024a0850140 0x800858024a085014 0x00018000e0000000 0x000018000e000000

def z519 : W := mkw 0x42102fffe0402948 0x842102fffe040294 0x40000fffe00039c4 0x140000fffe00039c

def z520 : W := mkw 0x0000000002001400 0x0000000000200140 0x300000001e003e08 0x0300000001e003e0

def z521 : W := mkw 0x89e5d0001db7c000 0x089e5d0001db7c00 0xb1f1f0001fffc009 0x0b1f1f0001fffc00

def z522 : W := mkw 0x40102365c0000000 0x040102365c000000 0x000001f0e0000000 0x0000001f0e000000

def z523 : W := mkw 0x0000b08160dc6314 0x40000b08160dc631 0x5003f003e1fce73a 0x05003f003e1fce73

def z524 : W := mkw 0x148f802ea48781e1 0x8148f802ea48781e 0x400f800fe007c1f2 0x0400f800fe007c1f

def z525 : W := mkw 0x4fef4c7e91010848 0x84fef4c7e9101084 0xafcc087c100318c0 0x5afcc087c100318c

def z526 : W := mkw 0x00c5803491850848 0x800c580349185084 0xa1cd887c11c718cb 0x7a1cd887c11c718c

def z527 : W := mkw 0x12c58cbeb3c53de9 0x812c58cbeb3c53de 0xe1cd8ffff1c73fff 0x7e1cd8ffff1c73ff

def z528 : W := mkw 0x0000009000402808 0x0000000900040280 0x000009f000003804 0x1000009f00000380

def z529 : W := mkw 0x061a2f0b40000000 0x0061a2f0b4000000 0x4e3fff8fe0000007 0xf4e3fff8fe000000

def z530 : W := mkw 0x8def40001d238000 0x08def40001d23800 0xbffc00001ffb0009 0xebffc00001ffb000

def z531 : W := mkw 0x4bb56f65c0000000 0x04bb56f65c000000 0x8ff1fff0e0000005 0xf8ff1fff0e000000

def z532 : W := mkw 0x06cf8cbeb1c52948 0x806cf8cbeb1c5294 0xefcf8ffff1c739cf 0xfefcf8ffff1c739c

def z533 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x1033f180e1fcc00b 0xa1033f180e1fcc00

def z534 : W := mkw 0x568f6c2fc60294a1 0x0568f6c2fc60294a 0x7e0ffe0ffe07fffe 0xf7e0ffe0ffe07fff

def z535 : W := mkw 0x0000b00160944110 0x40000b0016094411 0x5003f603e004e73e 0xa5003f603e004e73

def z536 : W := mkw 0x0000800000840000 0x0000080000084000 0x0001800001c4000b 0x20001800001c4000

def z537 : W := mkw 0x8defd0349db7c848 0x88defd0349db7c84 0xbffff87c1fffd8cb 0xfbffff87c1fffd8c

def z538 : W := mkw 0x16cf8cbeb7c7bde9 0x816cf8cbeb7c7bde 0xefcd89fcffc739cf 0x7efcd89fcffc739c

def z539 : W := mkw 0x1040809037c7bde9 0x81040809037c7bde 0x300000001fc7fff8 0x0300000001fc7fff

def z540 : W := mkw 0x4fffef6fd1850000 0x04fffef6fd185000 0xeffffffff1c7000f 0xfeffffffff1c7000

def z541 : W := mkw 0x2b700f501b201c0a 0x02b700f501b201c0 0xaff00ff01e001805 0xfaff00ff01e00180

def z542 : W := mkw 0x0010838020cc2304 0x00010838020cc230 0x50318780e1fc270f 0xa50318780e1fc270

def z543 : W := mkw 0x0010330140184214 0x4001033014018421 0x5033f783e038c637 0xa5033f783e038c63

def z544 : W := mkw 0x0010238140482204 0x0001023814048220 0x5033f783e1f8260f 0xa5033f783e1f8260

def z545 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0xc1f3f7f3e0000007 0xac1f3f7f3e000000

def z546 : W := mkw 0x0010330140184214 0x4001033014018421 0x50327603003ce73e 0xa50327603003ce73

def z547 : W := mkw 0x20c580b4bbed3f4e 0x820c580b4bbed3f4 0xf1cd89fcffff3fcf 0x7f1cd89fcffff3fc

def z548 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x4003f783e004e736 0x04003f783e004e73

def z549 : W := mkw 0x0085002480000000 0x0008500248000000 0x81cc087c00000000 0x581cc087c0000000

def z550 : W := mkw 0x0000000000000000 0x0000000000000000 0x400c080c00000006 0x7400c080c0000000

def z551 : W := mkw 0x22500fd013483e0e 0x022500fd013483e0 0xa1c00ff011c03e0d 0x7a1c00ff011c03e0

def z552 : W := mkw 0x4fbfefefe0c42100 0x04fbfefefe0c4210 0xcfffffffe1c4210f 0xfcfffffffe1c4210

def z553 : W := mkw 0x000080b4a0c42948 0x8000080b4a0c4294 0x400189fce1c439cf 0x3400189fce1c439c

def z554 : W := mkw 0x4fbf7f6fc0184214 0x44fbf7f6fc018421 0xdfffffffe038c637 0xfdfffffffe038c63

def z555 : W := mkw 0x9f2a5c0a0e32d4a1 0x09f2a5c0a0e32d4a 0x1e3276030e38c630 0x81e3276030e38c63

def z556 : W := mkw 0x4faf6c6fc0000000 0x04faf6c6fc000000 0xcfcff87fe0000002 0x5cfcff87fe000000

def z557 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xa1cc087c11c739c8 0x5a1cc087c11c739c

def z558 : W := mkw 0x0010b3b5e0dc6b5c 0xc0010b3b5e0dc6b5 0x5033ffffe1fcffff 0xb5033ffffe1fcfff

def z559 : W := mkw 0x0000900000944000 0x0000090000094400 0x5033f60301fce73f 0xa5033f60301fce73

def z560 : W := mkw 0x849ff38164dfe314 0x4849ff38164dfe31 0x503ff783e1ffe73f 0xa503ff783e1ffe73

def z561 : W := mkw 0x2b708fd03bec3f0e 0x02b708fd03bec3f0 0xfff18ff0fffc3f0f 0xffff18ff0fffc3f0

def z562 : W := mkw 0x4f3a7f4b40184214 0x44f3a7f4b4018421 0x1e3276030038c630 0x81e3276030038c63

def z563 : W := mkw 0x800010000c32c000 0x0800010000c32c00 0x100000000e38c000 0x0100000000e38c00

def z564 : W := mkw 0x89e5d00019b54000 0x089e5d00019b5400 0xbff1f0001ff80009 0xebff1f0001ff8000

def z565 : W := mkw 0x0000000000000000 0x0000000000000000 0x1030000001f80009 0xa1030000001f8000

def z566 : W := mkw 0x4fbfef6fe0850140 0x84fbfef6fe085014 0xcfffffffe00701c7 0xfcfffffffe00701c

def z567 : W := mkw 0x6f3a6f4b4a281606 0x06f3a6f4b4a28160 0x1e3276030e380600 0x81e3276030e38060

def z568 : W := mkw 0x304000901f6abeaf 0x0304000901f6abea 0x300000001ffffff8 0x0300000001ffffff

def z569 : W := mkw 0x4bb56f6fc0000000 0x04bb56f6fc000000 0xc1f1ffffe0000005 0x1c1f1ffffe000000

def z570 : W := mkw 0x0000300140104010 0x4000030014010401 0x000270030000c030 0x0000270030000c03

def z571 : W := mkw 0x4faf4c6e80000000 0x04faf4c6e8000000 0xcfcd89fce0000007 0x7cfcd89fce000000

def z572 : W := mkw 0x00c500b491412848 0x800c500b49141284 0xa1cc09fc11c338cd 0x7a1cc09fc11c338c

def z573 : W := mkw 0x0000900020944110 0x4000090002094411 0x000000000004c130 0x0000000000004c13

def z574 : W := mkw 0x22400c901b683e0e 0x022400c901b683e0 0x3e000e001ff83e0c 0xf3e000e001ff83e0

def z575 : W := mkw 0x4ffffffff1dd6b5c 0xc4ffffffff1dd6b5 0xfffffffff1ffffff 0xffffffffff1fffff

def z576 : W := mkw 0x9fffff8b7ffff7b5 0x49fffff8b7ffff7b 0xffffff8fffffffff 0xfffffff8ffffffff

def z577 : W := mkw 0x0085002480000000 0x0008500248000000 0x81c181f0e0000001 0x081c181f0e000000

def z578 : W := mkw 0x22100f4002081606 0x022100f400208160 0x0000060000000600 0x0000006000000060

def z579 : W := mkw 0x0010338160586314 0x4001033816058631 0x50327783e038e734 0x850327783e038e73

def z580 : W := mkw 0x2050b3917bfc7f1e 0x42050b3917bfc7f1 0x7033f783fffcff3f 0xa7033f783fffcff3

def z581 : W := mkw 0x89e5400019210000 0x089e540001921000 0x81c0000000000000 0x081c000000000000

def z582 : W := mkw 0xadffd3d01dffea0e 0x0adffd3d01dffea0 0xbffff1f01fffc00b 0xebffff1f01fffc00

def z583 : W := mkw 0x12000c00060294a1 0x012000c00060294a 0x3e000e001e07fffc 0xf3e000e001e07fff

def z584 : W := mkw 0xa04090901ffffe0e 0x0a04090901ffffe0 0x300000001ffffe08 0x0300000001ffffe0

def z585 : W := mkw 0x49b5f3e5e0dc6314 0x449b5f3e5e0dc631 0x81f1f1f0e1f80001 0x081f1f1f0e1f8000

def z586 : W := mkw 0x4fbf6f6fc4028000 0x04fbf6f6fc402800 0xfffffffffe07c00f 0xffffffffffe07c00

def z587 : W := mkw 0x469f6f6fc0000000 0x0469f6f6fc000000 0x400fffffe0000006 0x1400fffffe000000

def z588 : W := mkw 0x2210bfd162dc7f1e 0x42210bfd162dc7f1 0x5033fff3e1fcff3f 0xb5033fff3e1fcff3

def z589 : W := mkw 0x448ff02fe0944110 0x4448ff02fe094411 0x400ff00fe004c132 0x0400ff00fe004c13

def z590 : W := mkw 0x02000c0002001400 0x002000c000200140 0x1e0006000e000600 0x81e0006000e00060

def z591 : W := mkw 0x0000008000482204 0x0000000800048220 0x1000000001f82608 0x01000000001f8260

def z592 : W := mkw 0x4faf4c6e80000000 0x04faf4c6e8000000 0x8ffff87c00000003 0xf8ffff87c0000000

def z593 : W := mkw 0x10000000060294a1 0x010000000060294a 0x700c080c1e07fffe 0x7700c080c1e07fff

def z594 : W := mkw 0x2bf50ff49b693e4e 0x82bf50ff49b693e4 0xbffc0ffc1ffb3ecd 0xfbffc0ffc1ffb3ec

def z595 : W := mkw 0x4fff6fffd1402808 0x04fff6fffd140280 0xeffffffff1c0380f 0xfeffffffff1c0380

def z596 : W := mkw 0x3fff8ffebfefbfef 0x83fff8ffebfefbfe 0xffff8fffffffffff 0xfffff8ffffffffff

def z597 : W := mkw 0x2b30bfc16afc7716 0x42b30bfc16afc771 0x5e33f783effce73f 0xa5e33f783effce73

def z598 : W := mkw 0x040a000004028000 0x0040a00000402800 0x7e0e080c1e07f9ce 0xf7e0e080c1e07f9c

def z599 : W := mkw 0x4b302f6fc0000000 0x04b302f6fc000000 0xcff00fffe0000005 0xfcff00fffe000000

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x400200030004c132 0x0400200030004c13

def z601 : W := mkw 0x2bf58ff4bbed3f4e 0x82bf58ff4bbed3f4 0xbff18ff0fff83e0d 0xfbff18ff0fff83e0

def z602 : W := mkw 0x4210bfefe0dc6314 0x44210bfefe0dc631 0x5033ffffe1fce73f 0xb5033ffffe1fce73

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x100206030000c630 0x8100206030000c63

def z604 : W := mkw 0x0000000000000000 0x0000000000000000 0x3e0000001e000008 0xe3e0000001e00000

def z605 : W := mkw 0x461a2f6fc0000000 0x0461a2f6fc000000 0x4e0e0fffe0000006 0xf4e0e0fffe000000

def z606 : W := mkw 0x4fff6f7fd1010848 0x84fff6f7fd101084 0xeffffffff00318c7 0xfeffffffff00318c

def z607 : W := mkw 0x00c5000011010000 0x000c500001101000 0xa1cc000010030000 0x4a1cc00001003000

def z608 : W := mkw 0x4fbfff6fc0944000 0x04fbfff6fc094400 0xdfffffffe1fcc00f 0xfdfffffffe1fcc00

def z609 : W := mkw 0x8defd024bdb7c140 0x88defd024bdb7c14 0xfffff00cffffc1cb 0xefffff00cffffc1c

def z610 : W := mkw 0x0000002480000000 0x0000000248000000 0x400009fce0000004 0x1400009fce000000

def z611 : W := mkw 0x4fbfffefe0dc6314 0x44fbfffefe0dc631 0xcfffffffe1f80007 0xfcfffffffe1f8000

def z612 : W := mkw 0x0010038000482204 0x0001003800048220 0x0000078000002604 0x0000007800000260

def z613 : W := mkw 0x804090001db7c000 0x0804090001db7c00 0x3033f0001fffc00b 0xa3033f0001fffc00

def z614 : W := mkw 0x04cf800015878000 0x004cf80001587800 0xbfcf80001fc7c00b 0xebfcf80001fc7c00

def z615 : W := mkw 0x1f3a0f4a060294a1 0x01f3a0f4a060294a 0xfffe0fff1e07ffff 0xffffe0fff1e07fff

def z616 : W := mkw 0x3f3a0f4a0e2a96a7 0x03f3a0f4a0e2a96a 0x7e3e0e0f1e3ffffe 0xf7e3e0e0f1e3ffff

def z617 : W := mkw 0x4daf602fc0000000 0x04daf602fc000000 0xcffff00fe0000003 0xecffff00fe000000

def z618 : W := mkw 0x00c58034b1850948 0x800c58034b185094 0xe1cd887cf00719c2 0x5e1cd887cf00719c

def z619 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0x81f00ff001f83e05 0x181f00ff001f83e0

def z620 : W := mkw 0x0000b08160d46110 0x40000b08160d4611 0x4003f183e1c4e13f 0x24003f183e1c4e13

def z621 : W := mkw 0x42000c6e80000000 0x042000c6e8000000 0x0000087c00000000 0x10000087c0000000

def z622 : W := mkw 0x00858024a0850140 0x800858024a085014 0xc1cd89fce00701c7 0x7c1cd89fce00701c

def z623 : W := mkw 0x9f2a5c0a0e32d4a1 0x09f2a5c0a0e32d4a 0x7e3e7e0f1e3ffffe 0xf7e3e7e0f1e3ffff

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0x0033f00000000003 0xa0033f0000000000

def z625 : W := mkw 0x32100fda02483eaf 0x032100fda02483ea 0x40000fff00003ff4 0x140000fff00003ff

def z626 : W := mkw 0x0960000019200000 0x0096000001920000 0xafc000001e000000 0x4afc000001e00000

def z627 : W := mkw 0x16cf8c0a178794a1 0x016cf8c0a178794a 0xffcf8e0f1fc7ffff 0xfffcf8e0f1fc7fff

def z628 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x0e0000000e000000 0x00e0000000e00000

def z629 : W := mkw 0x2970b3d179fc6b1e 0x42970b3d179fc6b1 0xd1f3f7f3e1fce73f 0xad1f3f7f3e1fce73

def z630 : W := mkw 0x8dffd3801dffe204 0x08dffd3801dffe20 0xbffff7801fffe60f 0xebffff7801fffe60

def z631 : W := mkw 0x449f632fc0000000 0x0449f632fc000000 0x403ff78fe0000007 0xa403ff78fe000000

def z632 : W := mkw 0x060a0c0a00000000 0x0060a0c0a0000000 0x5e0e0e0f0004e73e 0xf5e0e0e0f0004e73

def z633 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x3e0e080c1e07d8ca 0xf3e0e080c1e07d8c

def z634 : W := mkw 0x42102fefe0482314 0x442102fefe048231 0x40000fffe0002734 0x140000fffe000273

def z635 : W := mkw 0x168f0c2e860294a1 0x0168f0c2e860294a 0xffcf8ffffe07ffff 0xfffcf8ffffe07fff

def z636 : W := mkw 0x0010230140000000 0x0001023014000000 0x0032760300000000 0x8003276030000000

def z637 : W := mkw 0x9fefdcbebff7fde9 0x89fefdcbebff7fde 0xffffffffffffffff 0xffffffffffffffff

def z638 : W := mkw 0x0000808020c42100 0x00000808020c4210 0x50038783e1c4e73f 0xa50038783e1c4e73

def z639 : W := mkw 0x0085002480000000 0x0008500248000000 0x400d800ce0000002 0x0400d800ce000000

def z640 : W := mkw 0x10c580b4b7c7bde9 0x810c580b4b7c7bde 0xf1cd89fcffc7ffff 0x7f1cd89fcffc7fff

def z641 : W := mkw 0x4000202fc0000000 0x04000202fc000000 0x4000000fe0000000 0x04000000fe000000

def z642 : W := mkw 0x140a000a040280a1 0x0140a000a040280a 0x000200030000c030 0x0000200030000c03

def z643 : W := mkw 0x0095b3a5e0dc6314 0x40095b3a5e0dc631 0xd1ffffffe1fce73f 0xfd1ffffffe1fce73

def z644 : W := mkw 0x1faf4c0a060294a1 0x01faf4c0a060294a 0xfffffe0f1e07ffff 0xffffffe0f1e07fff

def z645 : W := mkw 0x00d583b4b1cd2b4c 0x800d583b4b1cd2b4 0xf1fd8ffcf1ff3fcf 0xff1fd8ffcf1ff3fc

def z646 : W := mkw 0x04cf80b4b5c7a948 0x804cf80b4b5c7a94 0xffcf89fcffc7f9cf 0xfffcf89fcffc7f9c

def z647 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0x600d800cf1c739ca 0x0600d800cf1c739c

def z648 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x3e0e0e0f1e03def0 0xd3e0e0e0f1e03def

def z649 : W := mkw 0x008580a4a0c52140 0x8008580a4a0c5214 0x400d818ce1c721cf 0x2400d818ce1c721c

def z650 : W := mkw 0x161a2f0b460294a1 0x0161a2f0b460294a 0x7e3fff8ffe07ffff 0xf7e3fff8ffe07fff

def z651 : W := mkw 0x00d5a3b5f1cd2b5c 0xc00d5a3b5f1cd2b5 0xe1cd8ffff1c73fff 0x7e1cd8ffff1c73ff

def z652 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x5e0e0e0f0e00c636 0xf5e0e0e0f0e00c63

def z653 : W := mkw 0x060a0c0006029400 0x0060a0c000602940 0x3e0e0e001e07fe0e 0xf3e0e0e001e07fe0

def z654 : W := mkw 0x00c5003491010848 0x800c500349101084 0xe1cc087c100739ce 0x7e1cc087c100739c

def z655 : W := mkw 0x0970038019682204 0x0097003801968220 0xbff007801ff8260d 0xebff007801ff8260

def z656 : W := mkw 0xafffdff4bfffff4e 0x8afffdff4bfffff4 0xfffffffcffffffcf 0xffffffffcffffffc

def z657 : W := mkw 0x0000b00160944110 0x40000b0016094411 0x5033f003e1fcc13b 0xa5033f003e1fcc13

def z658 : W := mkw 0x8dfff3b5fdffeb5c 0xc8dfff3b5fdffeb5 0xffffffffffffffff 0xffffffffffffffff

def z659 : W := mkw 0x361a0fda064abeaf 0x0361a0fda064abea 0x7e0e0fff1e07fffe 0xf7e0e0fff1e07fff

def z660 : W := mkw 0xc9f5f365d9b54000 0x0c9f5f365d9b5400 0x81f1f1f0e1f80001 0x081f1f1f0e1f8000

def z661 : W := mkw 0x140a000a040280a1 0x0140a000a040280a 0x500e060f0007e7fe 0xa500e060f0007e7f

def z662 : W := mkw 0x0defc00011850000 0x00defc0001185000 0xaffff00011c7000b 0xeaffff00011c7000

def z663 : W := mkw 0x40856025c0000000 0x040856025c000000 0x0001f000e0000000 0x00001f000e000000

def z664 : W := mkw 0x0960000019200000 0x0096000001920000 0x81f0000001f80001 0x081f0000001f8000

def z665 : W := mkw 0x9fefdc0a1fb7d4a1 0x09fefdc0a1fb7d4a 0xbffff6031fffc63b 0xebffff6031fffc63

def z666 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x4033f183e1fcc133 0x04033f183e1fcc13

def z667 : W := mkw 0x0000008000402000 0x0000000800040200 0x0000018001c0200d 0x20000018001c0200

def z668 : W := mkw 0x0b300fc000482204 0x00b300fc00048220 0x9ff00ff001f8260d 0xf9ff00ff001f8260

def z669 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x1031f780e1f8260d 0xa1031f780e1f8260

def z670 : W := mkw 0x0040009011402808 0x0004000901140280 0x81c001f001c00001 0x081c001f001c0000

def z671 : W := mkw 0x80c590b4bdf7e948 0x880c590b4bdf7e94 0xf1cd89fcfffff9cf 0x7f1cd89fcfffff9c

def z672 : W := mkw 0x89e5d00019b54000 0x089e5d00019b5400 0x91f3f00001fcc00b 0xa91f3f00001fcc00

def z673 : W := mkw 0x6fffeffffbed3f4e 0x86fffeffffbed3f4 0xffffffffffff3fcf 0xfffffffffffff3fc

def z674 : W := mkw 0x0010a38160c42100 0x00010a38160c4210 0x4033f783e1c4210f 0xa4033f783e1c4210

def z675 : W := mkw 0x6fef4c7e9b201c0a 0x06fef4c7e9b201c0 0xafcc087c1e001800 0x5afcc087c1e00180

def z676 : W := mkw 0x0010b30160944110 0x40010b3016094411 0x4033f783e004c137 0xa4033f783e004c13

def z677 : W := mkw 0xafef4c501f239c0a 0x0afef4c501f239c0 0xafcc08701e031800 0x5afcc08701e03180

def z678 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x3e0c0e0c1e033ecc 0xf3e0c0e0c1e033ec

def z679 : W := mkw 0x0040000011000000 0x0004000001100000 0xa1c0000011c00009 0x6a1c0000011c0000

def z680 : W := mkw 0xafffdf401fbfd606 0x0afffdf401fbfd60 0xbffff6001fffc60b 0xebffff6001fffc60

def z681 : W := mkw 0x4f3a6f6fc0000000 0x04f3a6f6fc000000 0x4e327fffe0000004 0x94e327fffe000000

def z682 : W := mkw 0x0000800020850140 0x8000080002085014 0x00000000000701c0 0x000000000000701c

def z683 : W := mkw 0x140a000a040280a1 0x0140a000a040280a 0x7e0e000f1e07c1fa 0xe7e0e000f1e07c1f

def z684 : W := mkw 0x160abc0b6696d5b1 0x4160abc0b6696d5b 0x7e0ffe0ffe07fffe 0xf7e0ffe0ffe07fff

def z685 : W := mkw 0x4f3a6f4b40000000 0x04f3a6f4b4000000 0x4e33f783e0000007 0xa4e33f783e000000

def z686 : W := mkw 0x02000c0002001400 0x002000c000200140 0x2e0008001e001800 0x52e0008001e00180

def z687 : W := mkw 0x8dfff3015db7c000 0x08dfff3015db7c00 0xfffff783ffffc00f 0xefffff783ffffc00

def z688 : W := mkw 0x8def40349d238848 0x88def40349d23884 0xafcc087c1e0318c0 0x5afcc087c1e0318c

def z689 : W := mkw 0x0040809031c52948 0x80040809031c5294 0xa1c009f011c739cd 0x7a1c009f011c739c

def z690 : W := mkw 0x8050b3817dffe314 0x48050b3817dffe31 0x7033f783ffffe73f 0xa7033f783ffffe73

def z691 : W := mkw 0xabf5dfd01bfd7e0e 0x0abf5dfd01bfd7e0 0xbff1fff01ff83e0d 0xfbff1fff01ff83e0

def z692 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x400e0e0f0007fff6 0x1400e0e0f0007fff

def z693 : W := mkw 0x140ab00b6496c1b1 0x4140ab00b6496c1b 0x400ff00fe007c1f2 0x0400ff00fe007c1f

def z694 : W := mkw 0x0010238160482314 0x4001023816048231 0x00000180e0000000 0x000000180e000000

def z695 : W := mkw 0x061abf8b60dc6314 0x4061abf8b60dc631 0x5e3fff8fe1fce73f 0xf5e3fff8fe1fce73

def z696 : W := mkw 0x1000000a000000a1 0x01000000a000000a 0x4000000f000001f0 0x04000000f000001f

def z697 : W := mkw 0x0defc0b4b1c52948 0x80defc0b4b1c5294 0xeffff9fcf1c739cf 0xfeffff9fcf1c739c

def z698 : W := mkw 0xcfefdc6e9db7c000 0x0cfefdc6e9db7c00 0xbffff87c1fffc00b 0xfbffff87c1fffc00

def z699 : W := mkw 0x4fffeffff1c52948 0x84fffeffff1c5294 0xcfffffffe1c00007 0xfcfffffffe1c0000

def z700 : W := mkw 0x02000c0002001400 0x002000c000200140 0x7e0c0e0c1e073fce 0xf7e0c0e0c1e073fc

def z701 : W := mkw 0x4fefccfeb1c52948 0x84fefccfeb1c5294 0xefcd89fcf1c739cf 0x7efcd89fcf1c739c

def z702 : W := mkw 0x0010b30140944000 0x00010b3014094400 0x5033f783e1fcc00f 0xa5033f783e1fcc00

def z703 : W := mkw 0x0000808020c42100 0x00000808020c4210 0x00018180e1c00001 0x000018180e1c0000

def z704 : W := mkw 0x0dafd00000944000 0x00dafd0000094400 0x9ffff00001fcc00b 0xe9ffff00001fcc00

def z705 : W := mkw 0x0000808020c42100 0x00000808020c4210 0x0000000001c42108 0x00000000001c4210

def z706 : W := mkw 0x2bf50ff49b683e0e 0x02bf50ff49b683e0 0xfffd8ffcfff83e0f 0xffffd8ffcfff83e0

def z707 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xeffffffffe07d9f7 0xfeffffffffe07d9f

def z708 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcfcfffffe0000006 0x5cfcfffffe000000

def z709 : W := mkw 0x00c500b4b1412948 0x800c500b4b141294 0xe1cd89fcf00339c7 0x7e1cd89fcf00339c

def z710 : W := mkw 0x2b702fd15b683e0e 0x02b702fd15b683e0 0xbff1fff0fff83e0d 0xfbff1fff0fff83e0

def z711 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xcfffffffee000007 0xfcfffffffee00000

def z712 : W := mkw 0x4bb56f6fc0000000 0x04bb56f6fc000000 0xc1f3ffffe0000007 0xbc1f3ffffe000000

def z713 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x7e33f783fffce73f 0xe7e33f783fffce73

def z714 : W := mkw 0x8d6ad0001db7c000 0x08d6ad0001db7c00 0x1e3270000ff8c000 0x81e3270000ff8c00

def z715 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0x81f3f7f3e0000001 0x881f3f7f3e000000

def z716 : W := mkw 0x5fbf6f6fc20014a1 0x05fbf6f6fc20014a 0xcfffffffe00018c7 0xfcfffffffe00018c

def z717 : W := mkw 0x0d6a400019200000 0x00d6a40001920000 0xbff270001ff80009 0xebff270001ff8000

def z718 : W := mkw 0x64cf60bfdb683e0e 0x064cf60bfdb683e0 0x700ff00ffff83e0a 0x0700ff00ffff83e0

def z719 : W := mkw 0x29f5b3f5f9fd6b5e 0xc29f5b3f5f9fd6b5 0x81f1f1f0e1f80001 0x081f1f1f0e1f8000

def z720 : W := mkw 0x9defd00a1db7c0a1 0x09defd00a1db7c0a 0xfffff80f1ffff9ff 0xffffff80f1ffff9f

def z721 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcfffffffe0002737 0xfcfffffffe000273

def z722 : W := mkw 0xc250bf6fddb7c000 0x0c250bf6fddb7c00 0x70000fffffffc00c 0x170000fffffffc00

def z723 : W := mkw 0x00952325c0000000 0x000952325c000000 0xc1fdf9fce0000007 0x7c1fdf9fce000000

def z724 : W := mkw 0x4b302f6fc0000000 0x04b302f6fc000000 0xcff3ffffe0000007 0xfcff3ffffe000000

def z725 : W := mkw 0x00858024a0850140 0x800858024a085014 0xe1cd89fcf00739cf 0x7e1cd89fcf00739c

def z726 : W := mkw 0xa69fdfd006dffe0e 0x0a69fdfd006dffe0 0x000ffff00007fe06 0x1000ffff00007fe0

def z727 : W := mkw 0x0960100019304000 0x0096010001930400 0xbff270001ff8c009 0xebff270001ff8c00

def z728 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x703ff783f1ffe73f 0xe703ff783f1ffe73

def z729 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0xd1f3f7f3e004e73f 0xad1f3f7f3e004e73

def z730 : W := mkw 0x0b302f4140000000 0x00b302f414000000 0x8ff1fff0e0000005 0xf8ff1fff0e000000

def z731 : W := mkw 0x3b700fda1b683eaf 0x03b700fda1b683ea 0xfff20fff1ffcffff 0xffff20fff1ffcfff

def z732 : W := mkw 0x20c580b4b9ed2b4e 0x820c580b4b9ed2b4 0xe1cd89fcf1ff39cf 0x7e1cd89fcf1ff39c

def z733 : W := mkw 0x4fbf6f6fc0010040 0x84fbf6f6fc001004 0xcfffffffe00300c7 0xfcfffffffe00300c

def z734 : W := mkw 0x8d2a50b4ac72e948 0x88d2a50b4ac72e94 0x5e3279fcee38f9c4 0x95e3279fcee38f9c

def z735 : W := mkw 0x5f3a7f4b461ad6b5 0x45f3a7f4b461ad6b 0x1e3276030e38c630 0x81e3276030e38c63

def z736 : W := mkw 0x52102fefe24837b5 0x452102fefe24837b 0x40000fffe0003ff4 0x140000fffe0003ff

def z737 : W := mkw 0x4fafdceea0dc6314 0x44fafdceea0dc631 0x9fcc087c01fce738 0x59fcc087c01fce73

def z738 : W := mkw 0x8dff63817d6ba314 0x48dff63817d6ba31 0xefcc0783fe032734 0x4efcc0783fe03273

def z739 : W := mkw 0x297003d019682a0e 0x0297003d019682a0 0xaff001f01ff80001 0x4aff001f01ff8000

def z740 : W := mkw 0x8defd0101db7c808 0x08defd0101db7c80 0xbffff8701fffd80b 0xfbffff8701fffd80

def z741 : W := mkw 0x0040909031dd6b5c 0xc0040909031dd6b5 0x1000000001fce738 0x01000000001fce73

def z742 : W := mkw 0x89e5d0001db7c000 0x089e5d0001db7c00 0xbff1f0001fffc009 0xebff1f0001fffc00

def z743 : W := mkw 0x89e5d00019b54000 0x089e5d00019b5400 0xaff1f0001ff80001 0x4aff1f0001ff8000

def z744 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xcfffffffe007fff7 0xfcfffffffe007fff

def z745 : W := mkw 0x00c5802491850000 0x000c580249185000 0xe1cd89fcf1c739cf 0x7e1cd89fcf1c739c

def z746 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x7033f783f1ffffff 0xa7033f783f1fffff

def z747 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffff0001ffff9cb 0xebffff0001ffff9c

def z748 : W := mkw 0x89e5d00019b54000 0x089e5d00019b5400 0xbffdf0001fff000b 0xebffdf0001fff000

def z749 : W := mkw 0x2b60bc517bb45d1a 0x42b60bc517bb45d1 0xefc3f873fe04d932 0x5efc3f873fe04d93

def z750 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xfffff00c1fffc1cb 0xefffff00c1fffc1c

def z751 : W := mkw 0x2b702fd15b683e1e 0x42b702fd15b683e1 0xbff00ff31ff83e3d 0xfbff00ff31ff83e3

def z752 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0x9ff00ff00ff83e05 0x99ff00ff00ff83e0

def z753 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0xffce0fff1e07ffff 0xfffce0fff1e07fff

def z754 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xaff009f01ff8380d 0x7aff009f01ff8380

def z755 : W := mkw 0x8defd0249db7c040 0x88defd0249db7c04 0xbffff00c1fffc0cb 0xebffff00c1fffc0c

def z756 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffff9f01fffc00f 0xfbffff9f01fffc00

def z757 : W := mkw 0x8defd0249db7c000 0x08defd0249db7c00 0xfffff9fcfffff9cf 0xffffff9fcfffff9c

def z758 : W := mkw 0x2b600c501b201c0a 0x02b600c501b201c0 0xbfc008701ff81808 0x5bfc008701ff8180

def z759 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xe1cd89fcf1c719c3 0x5e1cd89fcf1c719c

def z760 : W := mkw 0x8d2ad0000cb6c000 0x08d2ad0000cb6c00 0x1e3270000ffcc008 0x81e3270000ffcc00

def z761 : W := mkw 0x4bb56f6fc0000000 0x04bb56f6fc000000 0xc1fdffffe0000007 0x7c1fdffffe000000

def z762 : W := mkw 0x72102fffc2483eaf 0x072102fffc2483ea 0x40000fffe0003ff4 0x140000fffe0003ff

def z763 : W := mkw 0x2b600cd01b683e0e 0x02b600cd01b683e0 0xbfc00e701ff83e0c 0xfbfc00e701ff83e0

def z764 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbffc0ff01fff3e0f 0xfbffc0ff01fff3e0

def z765 : W := mkw 0x80c5d0b4b1d56948 0x880c5d0b4b1d5694 0xe1cdf9fcf1c739cf 0x7e1cdf9fcf1c739c

def z766 : W := mkw 0x2b700fda1b683e0e 0x02b700fda1b683e0 0xfff00fff1ff83e0d 0xffff00fff1ff83e0

def z767 : W := mkw 0xc48ff025c497c000 0x0c48ff025c497c00 0x000ff000e007c002 0x0000ff000e007c00

def z768 : W := mkw 0x00c500b4b1412948 0x800c500b4b141294 0xe1cc09fcf1c339cd 0x7e1cc09fcf1c339c

def z769 : W := mkw 0x4bb56f65c0000000 0x04bb56f65c000000 0x8ff1f9f0e0000001 0x58ff1f9f0e000000

def z770 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0x81f1f9f0e0000005 0x781f1f9f0e000000

def z771 : W := mkw 0x848fd0248497c040 0x8848fd0248497c04 0x000ff00c0007c0c2 0x0000ff00c0007c0c

def z772 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xdfffffffee07c7f7 0xfdfffffffee07c7f

def z773 : W := mkw 0xdf3a7f4b4e32d4a1 0x0df3a7f4b4e32d4a 0x1e3276030e38c630 0x81e3276030e38c63

def z774 : W := mkw 0x4dbf636fc0000000 0x04dbf636fc000000 0xc1fff7ffe0000007 0xac1fff7ffe000000

def z775 : W := mkw 0x0085002480000000 0x0008500248000000 0xc1fff9fce0000007 0xfc1fff9fce000000

def z776 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcffff7ffe0000003 0x8cffff7ffe000000

def z777 : W := mkw 0x16cf8cbeb7c7bde9 0x816cf8cbeb7c7bde 0x9fc387f3efc0c631 0x89fc387f3efc0c63

def z778 : W := mkw 0x0dbf6325c0000000 0x00dbf6325c000000 0xcfffffffe0000007 0xfcfffffffe000000

def z779 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffff8001ffff80f 0xfbffff8001ffff80

def z780 : W := mkw 0x4fbf6f6fc2001400 0x04fbf6f6fc200140 0xcfffffffe0003e07 0xfcfffffffe0003e0

def z781 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcfffffffe004210f 0xfcfffffffe004210

def z782 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xdfffffffee04e73f 0xfdfffffffee04e73

def z783 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff20ff01ffcfe0f 0xfbff20ff01ffcfe0

def z784 : W := mkw 0x548ff02fe496c1b1 0x4548ff02fe496c1b 0x400ff00fe007c1f2 0x0400ff00fe007c1f

def z785 : W := mkw 0x02500f9013483e0c 0x002500f9013483e0 0xbff00ff01ff83e0d 0xfbff00ff01ff83e0

def z786 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xf1cd89fcf1c7ffff 0x7f1cd89fcf1c7fff

def z787 : W := mkw 0x0960900019b44000 0x00960900019b4400 0xbff1f0001ff80009 0xebff1f0001ff8000

def z788 : W := mkw 0x9defd02ebdb7c1e1 0x89defd02ebdb7c1e 0xfffff00fffffc1fb 0xefffff00fffffc1f

def z789 : W := mkw 0x4dbf6365c0000000 0x04dbf6365c000000 0x8ff3f1f0e0000001 0x88ff3f1f0e000000

def z790 : W := mkw 0x0000b00160944110 0x40000b0016094411 0x5033f603e1fce73f 0xa5033f603e1fce73

def z791 : W := mkw 0x848fd0000497c000 0x0848fd0000497c00 0x3e3ff0001fffc00b 0xe3e3ff0001fffc00

def z792 : W := mkw 0x0040909031dc6b1c 0x40040909031dc6b1 0x3000000011fcff38 0x03000000011fcff3

def z793 : W := mkw 0x6bb56f65ca281606 0x06bb56f65ca28160 0x9ff1f7f0ee380601 0x89ff1f7f0ee38060

def z794 : W := mkw 0xd48ff02fc497c0a1 0x0d48ff02fc497c0a 0x400ff00fe007c1f2 0x0400ff00fe007c1f

def z795 : W := mkw 0x8defd0249db7c000 0x08defd0249db7c00 0xbffff87c1fffc00b 0xfbffff87c1fffc00

def z796 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xe1cd89fcf00739c6 0x5e1cd89fcf00739c

def z797 : W := mkw 0x0faf4c2e80000000 0x00faf4c2e8000000 0xcfffffffe0000007 0xfcfffffffe000000

def z798 : W := mkw 0x2b702fd17b683f1e 0x42b702fd17b683f1 0xfff3fff3fff83f3f 0xffff3fff3fff83f3

def z799 : W := mkw 0x2b300fc00a683606 0x02b300fc00a68360 0x9ff00ff00ff8260d 0xf9ff00ff00ff8260

def z800 : W := mkw 0x3d7a03da1d6aaaaf 0x03d7a03da1d6aaaa 0xc1fe01ff01ffc1f3 0x0c1fe01ff01ffc1f

def z801 : W := mkw 0x804090903dffeb5c 0xc804090903dffeb5 0x300000001ffffff8 0x0300000001ffffff

def z802 : W := mkw 0x3b702fdb7b683fbf 0x43b702fdb7b683fb 0xfff00ffffff83ffd 0xffff00ffffff83ff

def z803 : W := mkw 0x62102fffe2483f1e 0x462102fffe2483f1 0x40000fffe0003f34 0x140000fffe0003f3

def z804 : W := mkw 0x00c590b4b1d56958 0xc00c590b4b1d5695 0xe1cd89fcf1c7f9ff 0x7e1cd89fcf1c7f9f

def z805 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcfffffffe00039c7 0xfcfffffffe00039c

def z806 : W := mkw 0x0010b301409c4214 0x40010b301409c421 0x5033f783e1fcc63f 0xa5033f783e1fcc63

def z807 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xdfffffffee00fff7 0xfdfffffffee00fff

def z808 : W := mkw 0x9be5dc0a1bb554a1 0x09be5dc0a1bb554a 0xc1f1fe0f01f83ff5 0x1c1f1fe0f01f83ff

def z809 : W := mkw 0x9fef4c3e9f239ce9 0x89fef4c3e9f239ce 0xafcc087c1e0318c0 0x5afcc087c1e0318c

def z810 : W := mkw 0x2b700fd03b683f1e 0x42b700fd03b683f1 0xbff00ff01ff83f3d 0xfbff00ff01ff83f3

def z811 : W := mkw 0x8dafd0000cb6c000 0x08dafd0000cb6c00 0x9ffff0000ffcc00b 0xe9ffff0000ffcc00

def z812 : W := mkw 0x0d6a90001db6c000 0x00d6a90001db6c00 0xbffff0001fffc00b 0xebffff0001fffc00

def z813 : W := mkw 0x5fbf6f6fc00000a1 0x05fbf6f6fc00000a 0xcfffffffe00001f7 0xfcfffffffe00001f

def z814 : W := mkw 0x00d53335d1194a5c 0xc00d53335d1194a5 0xb1fe7e7f103bdef0 0xdb1fe7e7f103bdef

def z815 : W := mkw 0x0fbf6f4140000000 0x00fbf6f414000000 0xcffffff3e0000007 0xfcffffff3e000000

def z816 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xe1fff9fcf1c739cf 0xfe1fff9fcf1c739c

def z817 : W := mkw 0x2b600cd01b683e0e 0x02b600cd01b683e0 0xafc008701ff81800 0x5afc008701ff8180

def z818 : W := mkw 0x0970034019200000 0x0097003401920000 0xbff001f01ff80009 0xebff001f01ff8000

def z819 : W := mkw 0x008580b4a0c52948 0x8008580b4a0c5294 0xc1cd89fce00739c7 0x7c1cd89fce00739c

def z820 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xeffffffffe033ff7 0xfeffffffffe033ff

def z821 : W := mkw 0x4bb56f65c2001400 0x04bb56f65c200140 0xbff1fff0fe003e0d 0xfbff1fff0fe003e0

def z822 : W := mkw 0x008580a4a0c42100 0x0008580a4a0c4210 0xe1cd89fcf1c739cf 0x7e1cd89fcf1c739c

def z823 : W := mkw 0x4f7aefdb71c52948 0x84f7aefdb71c5294 0x2e32760311c739c8 0x82e32760311c739c

def z824 : W := mkw 0x0930234140000000 0x0093023414000000 0xc1f3f7f3e0000007 0xac1f3f7f3e000000

def z825 : W := mkw 0x4fbf6f6fc2001400 0x04fbf6f6fc200140 0xfffffffffe04ff3f 0xffffffffffe04ff3

def z826 : W := mkw 0x4fbf6f6fc4028000 0x04fbf6f6fc402800 0xcfffffffe007c007 0xfcfffffffe007c00

def z827 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xfff20ff31ff83e0f 0xffff20ff31ff83e0

def z828 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xaff00ff01ff83e05 0x5aff00ff01ff83e0

def z829 : W := mkw 0x161abf8b66def7b5 0x4161abf8b66def7b 0x2e3df98cfffb18c1 0x52e3df98cfffb18c

def z830 : W := mkw 0x4fbf6f6fc2001400 0x04fbf6f6fc200140 0xfffffffffe073fcf 0xffffffffffe073fc

def z831 : W := mkw 0x0b300fc002483604 0x00b300fc00248360 0xbff00ff01ff83e0d 0xfbff00ff01ff83e0

def z832 : W := mkw 0x0920900008b44000 0x00920900008b4400 0x1e33f0000ffcc00b 0xa1e33f0000ffcc00

def z833 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcffdf9fce0000007 0x7cffdf9fce000000

def z834 : W := mkw 0x8defd0349db7c848 0x88defd0349db7c84 0xfffff9fcffffd8cf 0xffffff9fcffffd8c

def z835 : W := mkw 0x2b700fd03b683f4e 0x82b700fd03b683f4 0xbff00ff01ff83fcd 0xfbff00ff01ff83fc

def z836 : W := mkw 0x12102f8b624837b5 0x412102f8b624837b 0x40000783e0002734 0x040000783e000273

def z837 : W := mkw 0x8defd0003db7c140 0x88defd0003db7c14 0xbffff0001fffc1cb 0xebffff0001fffc1c

def z838 : W := mkw 0x8040909035d7e948 0x88040909035d7e94 0x2000000011c7f9c8 0x02000000011c7f9c

def z839 : W := mkw 0x2b700fd03b683f0e 0x02b700fd03b683f0 0xfff00ff0fff83f0d 0xffff00ff0fff83f0

def z840 : W := mkw 0x8d2a50000c32c000 0x08d2a50000c32c00 0x1e3270000ff8c009 0xa1e3270000ff8c00

def z841 : W := mkw 0x297003d019682a0e 0x0297003d019682a0 0xbff009f01ff8380d 0xfbff009f01ff8380

def z842 : W := mkw 0x844a90001db7c000 0x0844a90001db7c00 0x3e3ff0001fffc00b 0xe3e3ff0001fffc00

def z843 : W := mkw 0x0960000019200000 0x0096000001920000 0xbff3f0001ff8000b 0xebff3f0001ff8000

def z844 : W := mkw 0x02102f8162483714 0x402102f816248371 0x40000f83e0003f34 0x140000f83e0003f3

def z845 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xe1cc09fcf1c739cc 0x5e1cc09fcf1c739c

def z846 : W := mkw 0x0010338140586214 0x4001033814058621 0x5033f783e1f8e63f 0xa5033f783e1f8e63

def z847 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbfc00ff01ff83e0c 0x5bfc00ff01ff83e0

def z848 : W := mkw 0x2b702fd15b683e0e 0x02b702fd15b683e0 0xfff3fff3fffcff3f 0xffff3fff3fffcff3

def z849 : W := mkw 0x80c590b4b9f56948 0x880c590b4b9f5694 0xe1cd89fcf1ff39cf 0x7e1cd89fcf1ff39c

def z850 : W := mkw 0x00c590b4b1d56948 0x800c590b4b1d5694 0xe1cff9fcf1c7f9cf 0x7e1cff9fcf1c7f9c

def z851 : W := mkw 0x848fd024a497c140 0x8848fd024a497c14 0x000ff000e007c002 0x0000ff000e007c00

def z852 : W := mkw 0x296000501920080a 0x0296000501920080 0xbff000701ff80009 0xebff000701ff8000

def z853 : W := mkw 0x5fbf6f6fc20014a1 0x05fbf6f6fc20014a 0xfffffffffe003fff 0xffffffffffe003ff

def z854 : W := mkw 0x164a9c9a37dffffd 0xc164a9c9a37dffff 0x7e0e0e0f1ffffffe 0xf7e0e0e0f1ffffff

def z855 : W := mkw 0x22409c903bfc7f1e 0x422409c903bfc7f1 0x7e020e031ffcff3e 0xf7e020e031ffcff3

def z856 : W := mkw 0x00c590b4b1d56948 0x800c590b4b1d5694 0xf1cd89fcf1fff9cf 0x7f1cd89fcf1fff9c

def z857 : W := mkw 0x4fbf6f6fc0080204 0x04fbf6f6fc008020 0xdfffffffe0380607 0xfdfffffffe038060

def z858 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff3fff01ff83e0f 0xfbff3fff01ff83e0

def z859 : W := mkw 0x6fbf6f6fca281606 0x06fbf6f6fca28160 0xfffffffffe383e0f 0xffffffffffe383e0

def z860 : W := mkw 0x449f632fc0000000 0x0449f632fc000000 0xc1ffffffe0000007 0xfc1ffffffe000000

def z861 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffff0001ffbc001 0xcbffff0001ffbc00

def z862 : W := mkw 0xcfbf6f6fcc228000 0x0cfbf6f6fcc22800 0xcfffffffee000007 0xfcfffffffee00000

def z863 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xa1cd89fcf1c338cd 0x7a1cd89fcf1c338c

def z864 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0xc1f1f7f3e0000005 0x0c1f1f7f3e000000

def z865 : W := mkw 0x2bb58f64aaad1746 0x82bb58f64aaad174 0x5e3d860cee3f07c2 0x85e3d860cee3f07c

def z866 : W := mkw 0x069f2f2fc0000000 0x0069f2f2fc000000 0xcfffffffe0000007 0xfcfffffffe000000

def z867 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xe1cf89fff1c7f9ff 0x7e1cf89fff1c7f9f

def z868 : W := mkw 0x3b700fda1b683eaf 0x03b700fda1b683ea 0xbff00ffc1ff83ecd 0xfbff00ffc1ff83ec

def z869 : W := mkw 0x0010b301609c4314 0x40010b301609c431 0x5033f603e1fcc73b 0xa5033f603e1fcc73

def z870 : W := mkw 0x8d6a50001d32c000 0x08d6a50001d32c00 0x9ff270000ff8c001 0x89ff270000ff8c00

def z871 : W := mkw 0x4dbf6365c4028000 0x04dbf6365c402800 0xbffff1f0fe07c00b 0xebffff1f0fe07c00

def z872 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbff3f0001fffc009 0x8bff3f0001fffc00

def z873 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xeffffffffe0739cf 0xfeffffffffe0739c

def z874 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffff80c1fffd8cb 0xfbffff80c1fffd8c

def z875 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0x9ffff0000fffc003 0x89ffff0000fffc00

def z876 : W := mkw 0x4dbf6365c0000000 0x04dbf6365c000000 0x81fff1f0e0000003 0x081fff1f0e000000

def z877 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0x8ffdfffce0000005 0xf8ffdfffce000000

def z878 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xaffff0001ffb0003 0xeaffff0001ffb000

def z879 : W := mkw 0x4fbf6f6fc4028000 0x04fbf6f6fc402800 0xdfffffffee00c007 0xfdfffffffee00c00

def z880 : W := mkw 0x0960000019200000 0x0096000001920000 0xbff009f01ff8000d 0xfbff009f01ff8000

def z881 : W := mkw 0x1faf4c2e860294a1 0x01faf4c2e860294a 0xfffffffffe07ffff 0xffffffffffe07fff

def z882 : W := mkw 0x008500b4a0402948 0x8008500b4a040294 0xe1cd89fcf00739cf 0x7e1cd89fcf00739c

def z883 : W := mkw 0x2b600c501b201c0a 0x02b600c501b201c0 0xaff008701ff81801 0x5aff008701ff8180

def z884 : W := mkw 0x4f3a6f4b40000000 0x04f3a6f4b4000000 0xcff3fff3e0000007 0xfcff3fff3e000000

def z885 : W := mkw 0x6fbf6f6fca201402 0x06fbf6f6fca20140 0xcfffffffee000007 0xfcfffffffee00000

def z886 : W := mkw 0x0010b38160dd6354 0xc0010b38160dd635 0x5033f783e1ffe7ff 0xa5033f783e1ffe7f

def z887 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0x8fffffffe0000001 0xd8fffffffe000000

def z888 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff009f01ff81809 0xfbff009f01ff8180

def z889 : W := mkw 0x22102fd142483e0e 0x022102fd142483e0 0x40000ff3e0003e04 0x140000ff3e0003e0

def z890 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0x8ff1f1f0e0000001 0xe8ff1f1f0e000000

def z891 : W := mkw 0x8960500019304000 0x0896050001930400 0xbff070001ff80009 0xebff070001ff8000

def z892 : W := mkw 0x0010b39160dc6b5c 0xc0010b39160dc6b5 0x5033f783e1fcffff 0xa5033f783e1fcfff

def z893 : W := mkw 0x4fbf6f6fc4028000 0x04fbf6f6fc402800 0xeffffffffe030007 0xfeffffffffe03000

def z894 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xfffc0ffc1ff83e0f 0xffffc0ffc1ff83e0

def z895 : W := mkw 0x448f602fc0000000 0x0448f602fc000000 0xc1cff1ffe0000003 0x0c1cff1ffe000000

def z896 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xeffffffff00318c7 0xfeffffffff00318c

def z897 : W := mkw 0x0010230140000000 0x0001023014000000 0xc1f3fff3e0000007 0xfc1f3fff3e000000

def z898 : W := mkw 0x040a90000496c000 0x0040a90000496c00 0x1e33f0000ffcc00b 0xa1e33f0000ffcc00

def z899 : W := mkw 0x00c500b491402808 0x000c500b49140280 0xe1cd89fcf1c739cf 0x7e1cd89fcf1c739c

def z900 : W := mkw 0x2b700fd01b693e4e 0x82b700fd01b693e4 0xbff00ff01ffb3ecd 0xfbff00ff01ffb3ec

def z901 : W := mkw 0x2b700fd019682a0e 0x02b700fd019682a0 0xbff00ff01ff8000d 0xfbff00ff01ff8000

def z902 : W := mkw 0x89f5f3b5f9fd6b5c 0xc89f5f3b5f9fd6b5 0x81f1f1f0e1f80001 0x081f1f1f0e1f8000

def z903 : W := mkw 0x00c500b4b1412948 0x800c500b4b141294 0xe1cc09fcf00739ce 0x7e1cc09fcf00739c

def z904 : W := mkw 0x4bb56f65c0000000 0x04bb56f65c000000 0xcffdfffce0000007 0xfcffdfffce000000

def z905 : W := mkw 0x8defd0349db7c848 0x88defd0349db7c84 0xfffff87c1ffff9cf 0xffffff87c1ffff9c

def z906 : W := mkw 0x0fbf4f6480000000 0x00fbf4f648000000 0xcffffffce0000007 0xfcffffffce000000

def z907 : W := mkw 0x8d6ad0001db7c000 0x08d6ad0001db7c00 0x3e33f0001fffc00b 0xa3e33f0001fffc00

def z908 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0xc1ffffffe0000007 0xfc1ffffffe000000

def z909 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xaffff0001fffc003 0x4affff0001fffc00

def z910 : W := mkw 0x4faf6c6fc0000000 0x04faf6c6fc000000 0xcfcff9ffe0000007 0x7cfcff9ffe000000

def z911 : W := mkw 0x4fbf6f6fc0080214 0x44fbf6f6fc008021 0xcfffffffe0000637 0xfcfffffffe000063

def z912 : W := mkw 0x4bb56f6fc0000000 0x04bb56f6fc000000 0x81f1f9fce0000001 0x181f1f9fce000000

def z913 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0x3e3ff0001fffc00a 0x83e3ff0001fffc00

def z914 : W := mkw 0xcfbf6f6fc4038000 0x0cfbf6f6fc403800 0xcfffffffe0030007 0xfcfffffffe003000

def z915 : W := mkw 0x8040909039f56948 0x88040909039f5694 0x0000000001f80000 0x00000000001f8000

def z916 : W := mkw 0x49b5636fc0000000 0x049b5636fc000000 0xc1f1f1ffe0000001 0x0c1f1f1ffe000000

def z917 : W := mkw 0x948fd02ea497c1e1 0x8948fd02ea497c1e 0x400ff00fe007c1f2 0x0400ff00fe007c1f

def z918 : W := mkw 0x0010238140482204 0x0001023814048220 0x5033f783e1fce73f 0xa5033f783e1fce73

def z919 : W := mkw 0x59b56365c60294a1 0x059b56365c60294a 0xb1f1f1f0fe07fff9 0x0b1f1f1f0fe07fff

def z920 : W := mkw 0x5fbf6f6fc20014a1 0x05fbf6f6fc20014a 0xdfffffffe004ffff 0xfdfffffffe004fff

def z921 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xfff00ff01ffc3f0f 0xffff00ff01ffc3f0

def z922 : W := mkw 0x6b702fdb5b683e0e 0x06b702fdb5b683e0 0xbff00ff31ff83e0d 0xfbff00ff31ff83e0

def z923 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xfffffffffe00000f 0xffffffffffe00000

def z924 : W := mkw 0x00c590b4b1dd6b5c 0xc00c590b4b1dd6b5 0xe1cd89fcf1ff39cf 0x7e1cd89fcf1ff39c

def z925 : W := mkw 0x2b600cd01b683e0e 0x02b600cd01b683e0 0xbff008701ff83e09 0xfbff008701ff83e0

def z926 : W := mkw 0xcdefd0649db7c000 0x0cdefd0649db7c00 0xbffff0701fffc00b 0xebffff0701fffc00

def z927 : W := mkw 0x89e5d00019b54000 0x089e5d00019b5400 0xbff3f0001ffcc00b 0xebff3f0001ffcc00

def z928 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x5033f783e1fcc733 0x85033f783e1fcc73

def z929 : W := mkw 0x5fbf6f6fc20014a1 0x05fbf6f6fc20014a 0xeffffffff0073fff 0xfeffffffff0073ff

def z930 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xfffffe0f1fffffff 0xffffffe0f1ffffff

def z931 : W := mkw 0x848fd0248497c000 0x0848fd0248497c00 0x400ff00ce007c002 0x0400ff00ce007c00

def z932 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0xc1f1f9fce0000005 0x1c1f1f9fce000000

def z933 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff00ff01ff81e01 0xdbff00ff01ff81e0

def z934 : W := mkw 0x364a9c9a3ffeffbf 0x4364a9c9a3ffeffb 0x7e0e0e0f1ffffffe 0xf7e0e0e0f1ffffff

def z935 : W := mkw 0x568f6c2fc60294a1 0x0568f6c2fc60294a 0xffcffffffe07ffff 0xfffcffffffe07fff

def z936 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xdfffffffe000c637 0xfdfffffffe000c63

def z937 : W := mkw 0x040a000004028000 0x0040a00000402800 0x7e0e0e0f1e07fffe 0xf7e0e0e0f1e07fff

def z938 : W := mkw 0xa04090903fffff1e 0x4a04090903fffff1 0x300000001fffff38 0x0300000001fffff3

def z939 : W := mkw 0x00c5003491010848 0x800c500349101084 0xe1cd89fcf00739cf 0x7e1cd89fcf00739c

def z940 : W := mkw 0x7f3a6f4b4e2a96a7 0x07f3a6f4b4e2a96a 0x1e3276030e38c630 0x81e3276030e38c63

def z941 : W := mkw 0x00952325c0000000 0x000952325c000000 0xf1fffffff007ffff 0xff1fffffff007fff

def z942 : W := mkw 0x0dafd0000496c000 0x00dafd0000496c00 0xbffff0001fffc00b 0xebffff0001fffc00

def z943 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xfffe0fff1fffffff 0xffffe0fff1ffffff

def z944 : W := mkw 0x0daf402480000000 0x00daf40248000000 0x8ffff1f0e0000003 0xe8ffff1f0e000000

def z945 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0x8ff1f0000ff80001 0x08ff1f0000ff8000

def z946 : W := mkw 0x12102fbfe2483ffd 0xc12102fbfe2483ff 0x40000fffe0003ff4 0x140000fffe0003ff

def z947 : W := mkw 0x0bb52f65c0000000 0x00bb52f65c000000 0xcfffffffe0000007 0xfcfffffffe000000

def z948 : W := mkw 0x148fb02fe497c1f1 0xc148fb02fe497c1f 0x400ff00fe007c1f2 0x0400ff00fe007c1f

def z949 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0x9ff007f00ff8260d 0xa9ff007f00ff8260

def z950 : W := mkw 0x0085002480000000 0x0008500248000000 0xe1cd89fcf00318c7 0x7e1cd89fcf00318c

def z951 : W := mkw 0x62102fffe2483f4e 0x862102fffe2483f4 0x40000fffe0003fc4 0x140000fffe0003fc

def z952 : W := mkw 0x7fbf6f6fce2a96a7 0x07fbf6f6fce2a96a 0xfffffffffe3fffff 0xffffffffffe3ffff

def z953 : W := mkw 0x0010b30140944000 0x00010b3014094400 0x5033f783e1fce73f 0xa5033f783e1fce73

def z954 : W := mkw 0x8d6ad0001db7c000 0x08d6ad0001db7c00 0xbff270001fffc009 0xebff270001fffc00

def z955 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xa1cd89fcf1c718cb 0x7a1cd89fcf1c718c

def z956 : W := mkw 0x8defd00a1db7c000 0x08defd00a1db7c00 0xfffff00f1fffc00b 0xefffff00f1fffc00

def z957 : W := mkw 0x00c590b4b1dd6b5c 0xc00c590b4b1dd6b5 0xf1cf8ffff1ffffff 0xff1cf8ffff1fffff

def z958 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffe70001fffc008 0xcbffe70001fffc00

def z959 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xaffdf9fcfe0318c1 0x5affdf9fcfe0318c

def z960 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0x81fdf1f0e0000003 0x681fdf1f0e000000

def z961 : W := mkw 0x844a90903df7e948 0x8844a90903df7e94 0x7e0e080c1ffff9ce 0xf7e0e080c1ffff9c

def z962 : W := mkw 0x304090903ffeffbf 0x4304090903ffeffb 0x300000001ffffff8 0x0300000001ffffff

def z963 : W := mkw 0x4dbf636fc0000000 0x04dbf636fc000000 0x81fdf1fce0000001 0x081fdf1fce000000

def z964 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xf1cf89fcf1c7f9cf 0xff1cf89fcf1c7f9c

def z965 : W := mkw 0x4bb56f6fc0000000 0x04bb56f6fc000000 0x81f1f7f3e0000001 0x081f1f7f3e000000

def z966 : W := mkw 0x3f3a3f4b4e3ad6b7 0x43f3a3f4b4e3ad6b 0x1e3276030e38c630 0x81e3276030e38c63

def z967 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x1033f783e1fce739 0x81033f783e1fce73

def z968 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x1033f783e1fcc63b 0xa1033f783e1fcc63

def z969 : W := mkw 0x5bb56f6fc20014a1 0x05bb56f6fc20014a 0xc1f1ffffe0003ff5 0x1c1f1ffffe0003ff

def z970 : W := mkw 0x0b700f401b201400 0x00b700f401b20140 0xbff00ff01ff83e0d 0xfbff00ff01ff83e0

def z971 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcffff9ffe0000003 0x5cffff9ffe000000

def z972 : W := mkw 0x4dbf636fc0000000 0x04dbf636fc000000 0xc1fff9ffe0000007 0x7c1fff9ffe000000

def z973 : W := mkw 0x09e5400019200000 0x009e540001920000 0xbff1f0001ff80009 0xebff1f0001ff8000

def z974 : W := mkw 0x0defc00019a50000 0x00defc00019a5000 0xbffff0001fff000b 0xebffff0001fff000

def z975 : W := mkw 0x2b702fd17b683f1e 0x42b702fd17b683f1 0xbff00ff0fff83e0d 0xfbff00ff0fff83e0

def z976 : W := mkw 0x00c500b491412848 0x800c500b49141284 0xe1cd89fcf1c338cf 0x7e1cd89fcf1c338c

def z977 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x503fff8fe1fce73f 0xf503fff8fe1fce73

def z978 : W := mkw 0x0010b39160dc6b1c 0x40010b39160dc6b1 0x5033fff3e1fcff3f 0xb5033fff3e1fcff3

def z979 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcff3f7f3e0000007 0xacff3f7f3e000000

def z980 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xf1cd8ffcf1c73fcf 0xff1cd8ffcf1c73fc

def z981 : W := mkw 0xc48ff02fe497c110 0x4c48ff02fe497c11 0x400ff00fe007c132 0x0400ff00fe007c13

def z982 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffdf0001fffc009 0x4bffdf0001fffc00

def z983 : W := mkw 0x00c5003491010848 0x800c500349101084 0xe1cc09fcf00318c4 0x5e1cc09fcf00318c

def z984 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xfffff180ffffc00f 0xefffff180ffffc00

def z985 : W := mkw 0x12009c0a029454a1 0x012009c0a029454a 0x5033fe0f01fcffff 0xb5033fe0f01fcfff

def z986 : W := mkw 0x5fbf6f6fc40280a1 0x05fbf6f6fc40280a 0xcfffffffe000c037 0xfcfffffffe000c03

def z987 : W := mkw 0x09e5900019b54000 0x009e5900019b5400 0xbffff0001fffc00b 0xebffff0001fffc00

def z988 : W := mkw 0x22102ff5e2483f5e 0xc22102ff5e2483f5 0x40000fffe0003ff4 0x140000fffe0003ff

def z989 : W := mkw 0x9defd00a1db7c0a1 0x09defd00a1db7c0a 0xbffff0031fffc03b 0xebffff0031fffc03

def z990 : W := mkw 0x5fbf6f6fc40280a1 0x05fbf6f6fc40280a 0xcfffffffe00300c7 0xfcfffffffe00300c

def z991 : W := mkw 0x0040909031dd6b5c 0xc0040909031dd6b5 0x2000000011ff39c8 0x02000000011ff39c

def z992 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0xc1fdf1fce0000003 0x0c1fdf1fce000000

def z993 : W := mkw 0x4bb56f65c0000000 0x04bb56f65c000000 0x81f1fff0e0000005 0x181f1fff0e000000

def z994 : W := mkw 0x42952f6fc0000000 0x042952f6fc000000 0xc1ffffffe0000007 0xfc1ffffffe000000

def z995 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff20ff31ff8fe3d 0xfbff20ff31ff8fe3

def z996 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xdfffffffe004c00f 0xfdfffffffe004c00

def z997 : W := mkw 0x0def40001d228000 0x00def40001d22800 0xbffff0001fffc00b 0xebffff0001fffc00

def z998 : W := mkw 0x0040909031d56948 0x80040909031d5694 0x3000000011fff9c8 0x03000000011fff9c

def z999 : W := mkw 0x00c580b4b9e52948 0x800c580b4b9e5294 0xf1cd89fcffff39cf 0x7f1cd89fcffff39c

def z1000 : W := mkw 0x00c500b4b1412948 0x800c500b4b141294 0xa1cc09fcf00318c0 0x5a1cc09fcf00318c

def z1001 : W := mkw 0x4fbf6f6fc6029400 0x04fbf6f6fc602940 0xfffffffffe07fe0f 0xffffffffffe07fe0

def z1002 : W := mkw 0x8d6ad0001db6c000 0x08d6ad0001db6c00 0xbff3f0001ffcc00b 0xebff3f0001ffcc00

def z1003 : W := mkw 0x40856025c0000000 0x040856025c000000 0xc1cdf9fce0000007 0x7c1cdf9fce000000

def z1004 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff009f01ff83e09 0x5bff009f01ff83e0

def z1005 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xeffffffff007000f 0xfeffffffff007000

def z1006 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xfffffffffe07c63f 0xffffffffffe07c63

def z1007 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xa1cd89fcf1c739c9 0x5a1cd89fcf1c739c

def z1008 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xe1cd8ffff1c73fff 0x7e1cd8ffff1c73ff

def z1009 : W := mkw 0x0040909031d56958 0xc0040909031d5695 0x2000000011c7f9f8 0x02000000011c7f9f

def z1010 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xfff18ff0fff83e0f 0xffff18ff0fff83e0

def z1011 : W := mkw 0x0040809031c42908 0x00040809031c4290 0xe1cd89fcf1c739cf 0x7e1cd89fcf1c739c

def z1012 : W := mkw 0x5f3a6f4b460294a1 0x05f3a6f4b460294a 0x0e3276030e000000 0x80e3276030e00000

def z1013 : W := mkw 0x00c590b4b1d56948 0x800c590b4b1d5694 0xf1fffffff1ffffff 0xff1fffffff1fffff

def z1014 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff00e701ff83e08 0xdbff00e701ff83e0

def z1015 : W := mkw 0x0040909031dd6b5c 0xc0040909031dd6b5 0x700e0e0f11fffffe 0xf700e0e0f11fffff

def z1016 : W := mkw 0x0b700fc019682204 0x00b700fc01968220 0xbff00ff01ff8260d 0xfbff00ff01ff8260

def z1017 : W := mkw 0x02000c0002001400 0x002000c000200140 0x7e0e0e0f1e07fffe 0xf7e0e0e0f1e07fff

def z1018 : W := mkw 0x2b702fd15b683e0e 0x02b702fd15b683e0 0xbff27ff31ff83e0d 0xfbff27ff31ff83e0

def z1019 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcffdffffe0000005 0x5cffdffffe000000

def z1020 : W := mkw 0x0defd00019b44000 0x00defd00019b4400 0xbffff0001ffcc00b 0xebffff0001ffcc00

def z1021 : W := mkw 0x2b700f401b281606 0x02b700f401b28160 0xbff00ff01ff8060d 0xfbff00ff01ff8060

def z1022 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xfffffffffe03def7 0xffffffffffe03def

def z1023 : W := mkw 0x8defd0349db7c848 0x88defd0349db7c84 0xbffff0701fffc00b 0xebffff0701fffc00

def z1024 : W := mkw 0x5dbf636fc40280a1 0x05dbf636fc40280a 0xc1fff1ffe007c1f3 0x0c1fff1ffe007c1f

def z1025 : W := mkw 0x00952325c0000000 0x000952325c000000 0x81f1f1f0e0000001 0x081f1f1f0e000000

def z1026 : W := mkw 0x964a9c9a3ff7fde9 0x8964a9c9a3ff7fde 0x7e0e0e0f1ffffffe 0xf7e0e0e0f1ffffff

def z1027 : W := mkw 0x5fbf6f6fc40280a1 0x05fbf6f6fc40280a 0xfffffffffe07c1ff 0xffffffffffe07c1f

def z1028 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffff6001fffe60f 0xebffff6001fffe60

def z1029 : W := mkw 0x8def40001d238000 0x08def40001d23800 0xbffff0001ffb000b 0xebffff0001ffb000

def z1030 : W := mkw 0x0970039019682a0c 0x00970039019682a0 0xbff00ff01ff83e0d 0xfbff00ff01ff83e0

def z1031 : W := mkw 0x2b600cd01b603c0a 0x02b600cd01b603c0 0xbff009f01ff8380d 0xfbff009f01ff8380

def z1032 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xeffffffff000380f 0xfeffffffff000380

def z1033 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0x9ff3f7f3ee00c631 0x89ff3f7f3ee00c63

def z1034 : W := mkw 0x8d6ad0001db7c000 0x08d6ad0001db7c00 0x3e3e70001fffc00a 0xe3e3e70001fffc00

def z1035 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x7e0e060f1e07fffa 0x87e0e060f1e07fff

def z1036 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x4033f783e1fce737 0x04033f783e1fce73

def z1037 : W := mkw 0x8d6a50001d32c000 0x08d6a50001d32c00 0x3e3270001ff8c008 0x83e3270001ff8c00

def z1038 : W := mkw 0x9defd00a1db7c0a1 0x09defd00a1db7c0a 0xbffff00c1fffc0cb 0xebffff00c1fffc0c

def z1039 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xdfffffffe1f8000f 0xfdfffffffe1f8000

def z1040 : W := mkw 0x2040909039fc6b1e 0x42040909039fc6b1 0x0000000001f80000 0x00000000001f8000

def z1041 : W := mkw 0x8d6a50001d32c000 0x08d6a50001d32c00 0xbffe70001fffc00b 0xebffe70001fffc00

def z1042 : W := mkw 0x8d2ad0000cb6c000 0x08d2ad0000cb6c00 0x1e33f0000ff8c001 0x81e33f0000ff8c00

def z1043 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x6e0e0e0f1e07fff6 0x56e0e0e0f1e07fff

def z1044 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xe1cd89fcf1c339c5 0x5e1cd89fcf1c339c

def z1045 : W := mkw 0x04cf90001597c000 0x004cf90001597c00 0xbffff0001fffc00b 0xebffff0001fffc00

def z1046 : W := mkw 0xcdefd02e9db7c000 0x0cdefd02e9db7c00 0xbffff00c1fffc00b 0xebffff00c1fffc00

def z1047 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xfffff0001fffe10f 0xefffff0001fffe10

def z1048 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0x81f3f1f0e0000003 0xa81f3f1f0e000000

def z1049 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x1033f783e1f8e63d 0xa1033f783e1f8e63

def z1050 : W := mkw 0x469f6f6fc0000000 0x0469f6f6fc000000 0xc1cfffffe0000007 0x7c1cfffffe000000

def z1051 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xe1cf8ffff1c739cf 0xfe1cf8ffff1c739c

def z1052 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x7033ff83f1fcff3f 0xf7033ff83f1fcff3

def z1053 : W := mkw 0x169f2f2fc60294a1 0x0169f2f2fc60294a 0xfffffffffe07ffff 0xffffffffffe07fff

def z1054 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffff6031fffc63b 0xebffff6031fffc63

def z1055 : W := mkw 0x8040909039f56948 0x88040909039f5694 0x2000000011ff39c8 0x02000000011ff39c

def z1056 : W := mkw 0x8defd034bdb7c948 0x88defd034bdb7c94 0xfffff87cffffd9cb 0xffffff87cffffd9c

def z1057 : W := mkw 0x6b706fd15b683e0e 0x06b706fd15b683e0 0xbff07ff01ff83e0d 0xfbff07ff01ff83e0

def z1058 : W := mkw 0x2040909039fc6b1e 0x42040909039fc6b1 0x1000000001fce738 0x01000000001fce73

def z1059 : W := mkw 0x2b700f501b281e0e 0x02b700f501b281e0 0xbff00e701ff81e09 0xfbff00e701ff81e0

def z1060 : W := mkw 0xdfef4c6e9f2394a1 0x0dfef4c6e9f2394a 0xafcc087c1e0318c0 0x5afcc087c1e0318c

def z1061 : W := mkw 0x297003d01b683e0e 0x0297003d01b683e0 0xbff001f01ff83e09 0xebff001f01ff83e0

def z1062 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbffc0ffc1ffb3ecd 0xfbffc0ffc1ffb3ec

def z1063 : W := mkw 0x00952325c0000000 0x000952325c000000 0xc1f3f7f3e0000007 0xac1f3f7f3e000000

def z1064 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x3e0e0e0f1e07fff8 0xd3e0e0e0f1e07fff

def z1065 : W := mkw 0x296000901b683e0e 0x0296000901b683e0 0xbff009f01ff83e0d 0xfbff009f01ff83e0

def z1066 : W := mkw 0x0960001019200808 0x0096000101920080 0xbff008701ff81809 0xfbff008701ff8180

def z1067 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xfffffffffe07d8cf 0xffffffffffe07d8c

def z1068 : W := mkw 0x22102fd142483e1e 0x422102fd142483e1 0x00000ff300003e34 0x100000ff300003e3

def z1069 : W := mkw 0x00c5803491850848 0x800c580349185084 0xe1cd89fcf1c718cf 0x7e1cd89fcf1c718c

def z1070 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0x8ff3fff3e0000005 0xf8ff3fff3e000000

def z1071 : W := mkw 0x4dbf636fc0000000 0x04dbf636fc000000 0xcffff1ffe0000003 0xecffff1ffe000000

def z1072 : W := mkw 0x2010b3d160dc6b1e 0x42010b3d160dc6b1 0x5033f7f3e1fce73f 0xa5033f7f3e1fce73

def z1073 : W := mkw 0x8defd024bdb7c140 0x88defd024bdb7c14 0xfffff9fcffffc1cf 0xffffff9fcffffc1c

def z1074 : W := mkw 0x1f3a2f4b460294a1 0x01f3a2f4b460294a 0xfffffffffe07ffff 0xffffffffffe07fff

def z1075 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x7e3ffe0f1e07ffff 0xf7e3ffe0f1e07fff

def z1076 : W := mkw 0x4fbf6f6fc4028000 0x04fbf6f6fc402800 0xfffffffffe07e73f 0xffffffffffe07e73

def z1077 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xfffffffff007ffff 0xffffffffff007fff

def z1078 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xfffff0031fffc13b 0xefffff0031fffc13

def z1079 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffdf0001ffb0009 0xebffdf0001ffb000

def z1080 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xdfffffffe000260f 0xfdfffffffe000260

def z1081 : W := mkw 0x8d2ad0000cb6c000 0x08d2ad0000cb6c00 0x3e3ff0001fffc00b 0xe3e3ff0001fffc00

def z1082 : W := mkw 0x3b700fd01b683eaf 0x03b700fd01b683ea 0xbff00ff01ff83ffd 0xfbff00ff01ff83ff

def z1083 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0x81fdf9fce0000001 0x581fdf9fce000000

def z1084 : W := mkw 0x22102fc162483716 0x422102fc16248371 0x40000783e0002734 0x040000783e000273

def z1085 : W := mkw 0x00c580b4b1cd2b5c 0xc00c580b4b1cd2b5 0xe1cd89fcf1c73fff 0x7e1cd89fcf1c73ff

def z1086 : W := mkw 0x0040909031dd6b5c 0xc0040909031dd6b5 0x0000000001f80000 0x00000000001f8000

def z1087 : W := mkw 0x0b600c901b603c08 0x00b600c901b603c0 0xbff00ff01ff83e0d 0xfbff00ff01ff83e0

def z1088 : W := mkw 0x00c590b4b1dd6b5c 0xc00c590b4b1dd6b5 0xf1fff9fcf1ffffff 0xff1fff9fcf1fffff

def z1089 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff00ff01ffcff3d 0xfbff00ff01ffcff3

def z1090 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0x81f1f7f0e0000005 0xa81f1f7f0e000000

def z1091 : W := mkw 0xa04090903fffff4e 0x8a04090903fffff4 0x300000001fffffc8 0x0300000001fffffc

def z1092 : W := mkw 0x4bb56f65c0000000 0x04bb56f65c000000 0x8ff1f7f0e0000001 0x88ff1f7f0e000000

def z1093 : W := mkw 0x62102ff5c2483e0e 0x062102ff5c2483e0 0x00000ff0e0003e04 0x100000ff0e0003e0

def z1094 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x7e0f8f8ffe07ffff 0xf7e0f8f8ffe07fff

def z1095 : W := mkw 0x8defd0101db7c848 0x88defd0101db7c84 0xbffff0001fffd8cb 0xebffff0001fffd8c

def z1096 : W := mkw 0x041a2381644aa314 0x4041a2381644aa31 0x7e0e0783fe07e73e 0xe7e0e0783fe07e73

def z1097 : W := mkw 0x8defd024bdb7c140 0x88defd024bdb7c14 0xfffff80cfffff9cf 0xffffff80cfffff9c

def z1098 : W := mkw 0x204090903bfc7f1e 0x4204090903bfc7f1 0x300000001ff83e08 0x0300000001ff83e0

def z1099 : W := mkw 0x4dbf6365c0000000 0x04dbf6365c000000 0xcffff9fce0000007 0xfcffff9fce000000

def z1100 : W := mkw 0x4bb56f65c0000000 0x04bb56f65c000000 0xcff3fff3e0000007 0xfcff3fff3e000000

def z1101 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbffff0001fffe73b 0xebffff0001fffe73

def z1102 : W := mkw 0x9defd00a1db7c0a1 0x09defd00a1db7c0a 0xfffff60f1fffe7ff 0xefffff60f1fffe7f

def z1103 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcff3ffffe0000005 0x9cff3ffffe000000

def z1104 : W := mkw 0x3b700fda1b683eaf 0x03b700fda1b683ea 0xfffc0fff1fff3fff 0xffffc0fff1fff3ff

def z1105 : W := mkw 0x848ff025e497c150 0xc848ff025e497c15 0x400ff00fe007c1f2 0x0400ff00fe007c1f

def z1106 : W := mkw 0x048f402480000000 0x0048f40248000000 0xc1cff9fce0000007 0x7c1cff9fce000000

def z1107 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff00ff01fff3fcd 0xfbff00ff01fff3fc

def z1108 : W := mkw 0xadefd0501db7c80a 0x0adefd0501db7c80 0xbffff0701fffc00b 0xebffff0701fffc00

def z1109 : W := mkw 0x8defd0249db7c000 0x08defd0249db7c00 0xbffff1f0ffffc00b 0xebffff1f0ffffc00

def z1110 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0x8ff001f00ff80001 0x08ff001f00ff8000

def z1111 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff007f01ff80609 0xebff007f01ff8060

def z1112 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xaffdf0001fff000b 0x6affdf0001fff000

def z1113 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xbff3f0001ff8c009 0xebff3f0001ff8c00

def z1114 : W := mkw 0x5fbf6f6fc40280a1 0x05fbf6f6fc40280a 0xeffffffff007f9ff 0xfeffffffff007f9f

def z1115 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x5033ff8fe1fcffff 0xb5033ff8fe1fcfff

def z1116 : W := mkw 0x804090903df7e948 0x8804090903df7e94 0x300000001fffc008 0x0300000001fffc00

def z1117 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xfff00ff31ff83f3d 0xffff00ff31ff83f3

def z1118 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0x9ffff0000ff8c003 0xe9ffff0000ff8c00

def z1119 : W := mkw 0x09a5402480000000 0x009a540248000000 0x81f1f1f0e0000001 0x081f1f1f0e000000

def z1120 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0x8ffff7f3e0000003 0xe8ffff7f3e000000

def z1121 : W := mkw 0xc48ff02fe497c140 0x8c48ff02fe497c14 0x400ff00fe007c1c2 0x0400ff00fe007c1c

def z1122 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0x9ff3f0000ffcc00b 0xa9ff3f0000ffcc00

def z1123 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xe1cd89fcf1c318c7 0x7e1cd89fcf1c318c

def z1124 : W := mkw 0x4fbf6f6fc2001400 0x04fbf6f6fc200140 0xeffffffffe001807 0xfeffffffffe00180

def z1125 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xfffff6031fffc00f 0xefffff6031fffc00

def z1126 : W := mkw 0x896090001db7c000 0x0896090001db7c00 0xbff3f0001fffc00b 0xebff3f0001fffc00

def z1127 : W := mkw 0x8defd00019b54000 0x08defd00019b5400 0xbffff0001ff8000b 0xebffff0001ff8000

def z1128 : W := mkw 0x2b600cd01b683e0e 0x02b600cd01b683e0 0xbfc009f01ff83e0d 0x7bfc009f01ff83e0

def z1129 : W := mkw 0x22400c901b683e0e 0x022400c901b683e0 0xbfc00ff01ff83e0d 0xfbfc00ff01ff83e0

def z1130 : W := mkw 0x32102fdb62483fbf 0x432102fdb62483fb 0x40000fffe0003ff4 0x140000fffe0003ff

def z1131 : W := mkw 0x0930234140000000 0x0093023414000000 0x81f1f1f0e0000001 0x081f1f1f0e000000

def z1132 : W := mkw 0x0b302f4142001400 0x00b302f414200140 0xfff3fff3fe04ff3f 0xffff3fff3fe04ff3

def z1133 : W := mkw 0x8defd0249db7c000 0x08defd0249db7c00 0xfffff00cffffc00b 0xefffff00cffffc00

def z1134 : W := mkw 0x00c5003491010848 0x800c500349101084 0xa1cd89fcf00318c1 0x5a1cd89fcf00318c

def z1135 : W := mkw 0x00c580b4b1cd2b4c 0x800c580b4b1cd2b4 0xf1cd89fcf1ff3fcf 0x7f1cd89fcf1ff3fc

def z1136 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x7e0c0e0f1e07fffc 0x57e0c0e0f1e07fff

def z1137 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x5033f783e1f8c637 0xa5033f783e1f8c63

def z1138 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x5033f783e1f8e735 0x85033f783e1f8e73

def z1139 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcfffffffe004c137 0xfcfffffffe004c13

def z1140 : W := mkw 0x3b700fda1b683eaf 0x03b700fda1b683ea 0xbff00ff31ff83e3d 0xfbff00ff31ff83e3

def z1141 : W := mkw 0x6fbf6f6fc2081606 0x06fbf6f6fc208160 0xcfffffffe0000607 0xfcfffffffe000060

def z1142 : W := mkw 0x4fbf6f6fc4028000 0x04fbf6f6fc402800 0xfffffffffe07f9cf 0xffffffffffe07f9c

def z1143 : W := mkw 0x62102fdb42483e0e 0x062102fdb42483e0 0x00000ff300003e04 0x100000ff300003e0

def z1144 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xcfffffffe00701c7 0xfcfffffffe00701c

def z1145 : W := mkw 0x4fbf6f65c0000000 0x04fbf6f65c000000 0x8ffffff0e0000007 0xf8ffffff0e000000

def z1146 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0xd1f3fff3e1fce73f 0xfd1f3fff3e1fce73

def z1147 : W := mkw 0x1040909037dffffd 0xc1040909037dffff 0x300000001ffffff8 0x0300000001ffffff

def z1148 : W := mkw 0x9defd0001db7c0a1 0x09defd0001db7c0a 0xbffff0001fffc1fb 0xebffff0001fffc1f

def z1149 : W := mkw 0x22102fd162483f1e 0x422102fd162483f1 0x00000ff0e0003e04 0x100000ff0e0003e0

def z1150 : W := mkw 0x4dbf6365c0000000 0x04dbf6365c000000 0xcffff7f3e0000007 0xecffff7f3e000000

def z1151 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0x8ff1f1f0e0000001 0x08ff1f1f0e000000

def z1152 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xfffffffffe00fe3f 0xffffffffffe00fe3

def z1153 : W := mkw 0x2b700f501b201c0a 0x02b700f501b201c0 0xbff00ff01ff8180d 0xfbff00ff01ff8180

def z1154 : W := mkw 0x8defd0001db7c000 0x08defd0001db7c00 0xfffff80c1fffc00f 0xffffff80c1fffc00

def z1155 : W := mkw 0x8def50001d33c000 0x08def50001d33c00 0xbffe70001ffbc009 0xebffe70001ffbc00

def z1156 : W := mkw 0x5fbf6f6fc60294a1 0x05fbf6f6fc60294a 0xfffffffffe033ecf 0xffffffffffe033ec

def z1157 : W := mkw 0x5fbf6f6fc20014a1 0x05fbf6f6fc20014a 0xcfffffffe0000637 0xfcfffffffe000063

def z1158 : W := mkw 0x2b702fd15b683e0e 0x02b702fd15b683e0 0xfff00ff3fff83e0d 0xffff00ff3fff83e0

def z1159 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xbff007f01ff83e09 0x8bff007f01ff83e0

def z1160 : W := mkw 0x468f6c2fc0000000 0x0468f6c2fc000000 0xcfcfffffe0000007 0xfcfcfffffe000000

def z1161 : W := mkw 0x4dbf636fc0000000 0x04dbf636fc000000 0x81f3f1f3e0000001 0x081f3f1f3e000000

def z1162 : W := mkw 0x0daf402484028000 0x00daf40248402800 0xfffff9fcfe07f9cf 0xffffff9fcfe07f9c

def z1163 : W := mkw 0xc48fd02e8497c000 0x0c48fd02e8497c00 0x000ff00c0007c002 0x0000ff00c0007c00

def z1164 : W := mkw 0x0000908020d46100 0x00000908020d4610 0x5033f783e1fce73f 0xa5033f783e1fce73

def z1165 : W := mkw 0x204090903bfd7f5e 0xc204090903bfd7f5 0x300000001ffffff8 0x0300000001ffffff

def z1166 : W := mkw 0x0f3a2f4b40000000 0x00f3a2f4b4000000 0xcfffffffe0000007 0xfcfffffffe000000

def z1167 : W := mkw 0x5fbf6f6fc40280a1 0x05fbf6f6fc40280a 0xdfffffffe007e7ff 0xfdfffffffe007e7f

def z1168 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0xe1fdf9fcf00739cf 0x7e1fdf9fcf00739c

def z1169 : W := mkw 0x0000900000944000 0x0000090000094400 0x3e33f0001ffcc00b 0xe3e33f0001ffcc00

def z1170 : W := mkw 0x160a0c0a060294a1 0x0160a0c0a060294a 0x7e3e0e0f1fffffff 0xf7e3e0e0f1ffffff

def z1171 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0xc1f1f1f0e0000007 0x2c1f1f1f0e000000

def z1172 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x503ff78fe1ffe7ff 0xa503ff78fe1ffe7f

def z1173 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0xc1ffffffe0000007 0x1c1ffffffe000000

def z1174 : W := mkw 0x6fbf6f6fc8280206 0x06fbf6f6fc828020 0xcfffffffe0380007 0xfcfffffffe038000

def z1175 : W := mkw 0x7fbf6f6fce2a96a7 0x07fbf6f6fce2a96a 0xdfffffffee38c637 0xfdfffffffee38c63

def z1176 : W := mkw 0x8defd0003db7c110 0x48defd0003db7c11 0xbffff0001fffc13b 0xebffff0001fffc13

def z1177 : W := mkw 0x4fbf6f6fc2001400 0x04fbf6f6fc200140 0xdfffffffee000607 0xfdfffffffee00060

def z1178 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xf1fd89fcf1ff39cf 0xff1fd89fcf1ff39c

def z1179 : W := mkw 0x49b56365c0000000 0x049b56365c000000 0xc1f3f1f3e0000003 0x0c1f3f1f3e000000

def z1180 : W := mkw 0x004000b4b1402948 0x8004000b4b140294 0xe1cc09fcf1c739cf 0x7e1cc09fcf1c739c

def z1181 : W := mkw 0x297003d019682a0e 0x0297003d019682a0 0x9ff001f00ff80001 0x89ff001f00ff8000

def z1182 : W := mkw 0x7fef4c7e9f229cab 0x07fef4c7e9f229ca 0xafcc087c1e0318c0 0x5afcc087c1e0318c

def z1183 : W := mkw 0x00c58034b1850948 0x800c58034b185094 0xe1cd89fcf00719c7 0x7e1cd89fcf00719c

def z1184 : W := mkw 0x40856025c0000000 0x040856025c000000 0x81c1f1f0e0000001 0x081c1f1f0e000000

def z1185 : W := mkw 0x4bb56f6fc0000000 0x04bb56f6fc000000 0xcff1ffffe0000005 0xfcff1ffffe000000

def z1186 : W := mkw 0x09a5402480000000 0x009a540248000000 0xc1fdf9fce0000007 0x7c1fdf9fce000000

def z1187 : W := mkw 0x4fbf6f6fc0000000 0x04fbf6f6fc000000 0x8ffff9fce0000003 0xf8ffff9fce000000

def z1188 : W := mkw 0x00c590b4b1d56948 0x800c590b4b1d5694 0xe1fdf9fcf1ff39cf 0x7e1fdf9fcf1ff39c

def z1189 : W := mkw 0x8def50001d32c000 0x08def50001d32c00 0xbffff0001ff8c00b 0xebffff0001ff8c00

def z1190 : W := mkw 0x8defd0003db7c100 0x08defd0003db7c10 0xfffff000ffffc10b 0xefffff000ffffc10

def z1191 : W := mkw 0x4faf4c6e80000000 0x04faf4c6e8000000 0xcffff9fce0000007 0xfcffff9fce000000

def z1192 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xaff00ff01ff81805 0xfaff00ff01ff8180

def z1193 : W := mkw 0x2b600c501b201c0a 0x02b600c501b201c0 0xbff00e701ff83e0d 0xfbff00e701ff83e0

def z1194 : W := mkw 0x4dbf6365c0000000 0x04dbf6365c000000 0x8ffdf1f0e0000001 0x48ffdf1f0e000000

def z1195 : W := mkw 0x0960009019602808 0x0096000901960280 0xbff001f01ff80009 0xebff001f01ff8000

def z1196 : W := mkw 0x0010b38160dc6314 0x40010b38160dc631 0x5033f603e1fce73a 0x85033f603e1fce73

def z1197 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xffcd89fcffc739cf 0xfffcd89fcffc739c

def z1198 : W := mkw 0x0b600c4019200000 0x00b600c401920000 0xbff008701ff80009 0xfbff008701ff8000

def z1199 : W := mkw 0x0b700fd019602808 0x00b700fd01960280 0xbff00ff01ff8380d 0xfbff00ff01ff8380

def z1200 : W := mkw 0x297003d019682a0e 0x0297003d019682a0 0xbff007f01ff8260d 0xebff007f01ff8260

def z1201 : W := mkw 0x904090903ff7fde9 0x8904090903ff7fde 0x300000001ffffff8 0x0300000001ffffff

def z1202 : W := mkw 0x69b56365c8280206 0x069b56365c828020 0x81f1f1f0e0380001 0x081f1f1f0e038000

def z1203 : W := mkw 0x00852025c0000000 0x000852025c000000 0xc1cff9ffe0000007 0x7c1cff9ffe000000

def z1204 : W := mkw 0x8defd024bdb7c140 0x88defd024bdb7c14 0xbffff000ffffc00b 0xebffff000ffffc00

def z1205 : W := mkw 0x8dafd0000cb7c000 0x08dafd0000cb7c00 0x1e3ff0000fffc00b 0xa1e3ff0000fffc00

def z1206 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0xfff00ffc1ff83fcd 0xffff00ffc1ff83fc

def z1207 : W := mkw 0x89e5d00019b54000 0x089e5d00019b5400 0x9ff1f0000ff80001 0x89ff1f0000ff8000

def z1208 : W := mkw 0x4daf602fc0000000 0x04daf602fc000000 0xcffff9ffe0000007 0xfcffff9ffe000000

def z1209 : W := mkw 0x00c580b4b1c52948 0x800c580b4b1c5294 0xc1cd89fce1c739c7 0x1c1cd89fce1c739c

def z1210 : W := mkw 0x2b700fd01b683e0e 0x02b700fd01b683e0 0x9ff00ff00ff80605 0xf9ff00ff00ff8060

def z1211 : W := mkw 0x4fbf6f6fc8200000 0x04fbf6f6fc820000 0xdfffffffee380007 0xfdfffffffee38000

def z1212 : W := mkw 0x548f602fc40280a1 0x0548f602fc40280a 0xe1cff9fff007f9ff 0x7e1cff9fff007f9f

def z1213 : W := mkw 0x2b702fd17b683f1e 0x42b702fd17b683f1 0xfff20ff3fffcff3f 0xffff20ff3fffcff3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z6,z2,z7,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z8,z5]),(0,[z0,z6,z2,z3,z4,z5,z9])],[(1,[z10,z11,z2,z3,z4,z5]),(0,[z0,z6,z12,z2,z3,z4,z5]),(0,[z13,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z14,z2,z3,z4,z5]),(0,[z15,z0,z6,z16,z2,z3,z5]),(0,[z0,z6,z2,z3,z17,z4,z5]),(1,[z0,z6,z18,z2,z4,z5])],[(0,[z19,z0,z6,z2,z3,z4,z5]),(0,[z20,z0,z6,z2,z21,z3,z5]),(0,[z22,z0,z6,z2,z3,z4,z5]),(0,[z23,z0,z6,z2,z3,z24,z5]),(0,[z0,z6,z2,z3,z4,z5,z25])],[(0,[z0,z6,z2,z3,z4,z26,z5]),(0,[z0,z6,z27,z2,z3,z4,z5]),(0,[z0,z6,z2,z21,z3,z28,z5]),(0,[z0,z29,z6,z2,z3,z4,z5])],[(1,[z0,z6,z30,z2,z3,z4]),(0,[z31,z0,z6,z2,z32,z4,z5]),(0,[z0,z6,z33,z2,z3,z4,z5]),(0,[z20,z0,z6,z2,z3,z34,z5]),(0,[z0,z6,z2,z3,z4,z35,z5]),(0,[z0,z6,z16,z2,z3,z4,z5]),(0,[z0,z36,z6,z2,z3,z4,z5])],[(0,[z0,z37,z6,z2,z3,z4,z5]),(0,[z0,z6,z38,z2,z39,z4,z5]),(0,[z0,z6,z2,z3,z34,z28,z5]),(0,[z0,z6,z40,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z4,z41,z5]),(0,[z0,z6,z42,z2,z3,z4,z5]),(0,[z0,z6,z43,z2,z3,z4,z5])],[(0,[z44,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z45,z5]),(0,[z0,z6,z2,z46,z3,z24,z5])]],
   [[(0,[z0,z47,z6,z2,z3,z28,z5])],[(0,[z0,z6,z48,z2,z3,z4,z5]),(0,[z0,z6,z2,z49,z3,z4,z5]),(1,[z0,z6,z2,z50,z4,z5]),(0,[z0,z6,z2,z51,z3,z4,z5]),(0,[z0,z6,z52,z2,z3,z4,z5]),(0,[z0,z6,z2,z53,z3,z4,z5]),(0,[z0,z6,z2,z54,z3,z4,z5])],[(0,[z0,z55,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z56,z4,z5]),(0,[z0,z6,z2,z3,z4,z57,z58]),(0,[z0,z6,z2,z46,z3,z4,z58])],[(0,[z0,z6,z2,z3,z59,z4,z5]),(0,[z0,z6,z2,z60,z3,z4,z5]),(0,[z0,z6,z61,z2,z3,z4,z5]),(0,[z0,z6,z62,z2,z3,z4,z5]),(1,[z0,z6,z63,z3,z24,z5]),(0,[z0,z6,z2,z3,z4,z64,z5]),(0,[z0,z6,z2,z3,z4,z5,z65])],[(0,[z0,z6,z2,z3,z24,z4,z5])],[(0,[z0,z6,z66,z2,z3,z24,z5]),(0,[z0,z6,z2,z3,z67,z4,z5])],[(0,[z68,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z69]),(0,[z0,z6,z38,z2,z32,z4,z5]),(0,[z0,z70,z6,z2,z3,z24,z5]),(0,[z0,z71,z6,z2,z3,z4,z5]),(0,[z0,z6,z72,z2,z3,z4,z57]),(0,[z0,z6,z2,z3,z4,z5,z73])],[(0,[z6,z2,z3,z34,z4,z74,z5]),(0,[z75,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z76,z5]),(0,[z0,z6,z2,z3,z4,z77,z5]),(0,[z0,z6,z78,z2,z3,z4,z5]),(0,[z0,z79,z6,z2,z4,z80,z5]),(0,[z0,z6,z2,z3,z4,z81,z5])]],
   [[(1,[z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z82,z2,z3,z4,z5]),(0,[z0,z6,z83,z2,z3,z4,z5]),(0,[z0,z6,z84,z2,z3,z28,z5])],[(0,[z0,z6,z2,z3,z4,z85,z5]),(0,[z0,z6,z2,z86,z3,z4,z5]),(1,[z0,z87,z2,z3,z4,z5]),(0,[z0,z2,z3,z88,z4,z89,z5])],[(0,[z0,z6,z90,z2,z3,z4,z5]),(0,[z0,z6,z91,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z92,z5]),(0,[z0,z93,z6,z2,z3,z4,z5]),(0,[z0,z6,z16,z2,z3,z24,z5])],[(0,[z0,z37,z6,z11,z2,z3,z5]),(0,[z0,z55,z2,z94,z3,z4,z5]),(0,[z0,z6,z95,z2,z3,z4,z5]),(0,[z0,z6,z38,z2,z4,z5,z96])],[(0,[z0,z6,z2,z3,z4,z97,z5]),(0,[z98,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z94,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z99,z5]),(0,[z0,z6,z2,z3,z4,z5,z100])],[(0,[z10,z0,z6,z2,z3,z24,z5]),(0,[z0,z6,z101,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z102,z4,z5]),(0,[z0,z6,z72,z2,z3,z103,z5]),(0,[z0,z6,z2,z3,z4,z104,z5])],[(0,[z0,z6,z105,z2,z3,z4,z5]),(0,[z0,z6,z2,z106,z3,z4,z5]),(0,[z0,z6,z2,z3,z24,z5,z96])],[(0,[z20,z0,z47,z6,z2,z3,z5]),(0,[z0,z6,z107,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z108,z5]),(0,[z109,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z110,z2,z3,z4,z5]),(0,[z0,z6,z2,z4,z111,z5,z112]),(0,[z0,z6,z2,z3,z4,z5,z113]),(0,[z0,z6,z2,z3,z4,z114,z5]),(0,[z115,z0,z6,z2,z3,z4,z5]),(0,[z116,z0,z6,z2,z3,z4,z5])]],
   [[(0,[z0,z55,z6,z2,z3,z24,z5]),(1,[z98,z6,z117,z3,z4,z5]),(0,[z20,z0,z6,z2,z3,z74,z5]),(0,[z15,z0,z118,z2,z3,z4,z5]),(0,[z0,z119,z6,z2,z3,z4,z5]),(0,[z0,z6,z120,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z121,z5])],[(0,[z122,z0,z6,z2,z3,z24,z5]),(0,[z0,z6,z123,z2,z3,z4,z5])],[(0,[z0,z6,z124,z2,z3,z4,z5]),(0,[z0,z6,z2,z125,z3,z4,z5]),(0,[z0,z6,z2,z126,z3,z4,z5]),(0,[z0,z127,z79,z2,z3,z4,z5]),(0,[z0,z6,z128,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z24,z24,z5]),(0,[z0,z6,z16,z2,z21,z4,z5]),(0,[z0,z6,z2,z129,z3,z4,z5])],[(0,[z0,z130,z6,z2,z3,z4,z5]),(0,[z0,z131,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z58,z132])],[(0,[z0,z133,z6,z2,z3,z4,z5]),(0,[z0,z6,z134,z2,z3,z135,z5])],[(0,[z0,z6,z136,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z137]),(0,[z138,z0,z6,z2,z3,z4,z5]),(0,[z0,z139,z6,z2,z3,z24,z5]),(0,[z0,z6,z2,z46,z4,z80,z5])],[(0,[z0,z6,z2,z140,z3,z4,z5]),(0,[z20,z0,z6,z2,z50,z4,z5]),(0,[z20,z6,z2,z3,z4,z74,z5]),(1,[z0,z6,z2,z3,z24,z5]),(0,[z0,z6,z63,z2,z3,z24,z5]),(0,[z0,z6,z141,z2,z3,z4,z5])],[(0,[z0,z6,z142,z2,z117,z3,z4]),(0,[z0,z6,z2,z143,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z144]),(0,[z0,z6,z2,z3,z28,z145,z5]),(0,[z0,z6,z38,z2,z146,z4,z5])]],
   [[(0,[z138,z31,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z147,z4,z5]),(0,[z0,z6,z2,z3,z4,z148,z112]),(0,[z149,z0,z6,z2,z3,z4,z5]),(0,[z0,z93,z6,z2,z3,z24,z5]),(0,[z0,z6,z72,z2,z3,z4,z132])],[(0,[z150,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z151,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z28,z148,z5])],[(0,[z98,z0,z6,z2,z3,z24,z5]),(0,[z152,z6,z66,z2,z3,z4,z5]),(0,[z153,z0,z6,z2,z3,z4,z5]),(1,[z0,z6,z154,z155,z4,z5]),(0,[z0,z6,z2,z3,z4,z156,z5])],[(1,[z0,z157,z2,z3,z4,z5]),(0,[z158,z159,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z160,z5]),(0,[z0,z6,z2,z3,z4,z5,z161]),(0,[z162,z0,z6,z2,z3,z4,z5])],[(0,[z98,z6,z2,z117,z3,z4,z5]),(0,[z15,z0,z6,z2,z21,z3,z5]),(0,[z0,z6,z2,z3,z28,z5,z163]),(0,[z0,z6,z2,z3,z4,z5,z164]),(0,[z0,z6,z2,z3,z165,z4,z5]),(0,[z0,z6,z2,z3,z24,z88,z5]),(1,[z0,z6,z2,z4,z111,z5]),(0,[z0,z6,z166,z2,z3,z4,z5]),(0,[z0,z167,z6,z2,z3,z4,z5])],[(0,[z0,z6,z2,z168,z3,z39,z4]),(0,[z20,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z169,z2,z3,z4,z5]),(0,[z170,z0,z6,z2,z3,z4,z5])],[(0,[z0,z47,z6,z2,z3,z4,z160])],[(0,[z171,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z172,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z173]),(0,[z0,z139,z6,z2,z3,z88,z5]),(0,[z0,z174,z6,z2,z3,z4,z5]),(1,[z0,z6,z175,z176,z4,z5]),(0,[z0,z6,z38,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z177,z4,z5]),(0,[z0,z6,z2,z3,z4,z178,z5])]],
   [[(0,[z179,z0,z2,z3,z4,z58,z5]),(0,[z0,z180,z6,z2,z3,z4,z5])],[(0,[z0,z181,z6,z2,z3,z4,z5]),(0,[z0,z182,z6,z2,z3,z4,z5])],[(0,[z0,z139,z47,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z183,z4,z5])],[(0,[z0,z6,z2,z184,z3,z4,z5]),(0,[z138,z0,z6,z2,z3,z24,z5]),(0,[z0,z6,z2,z3,z185,z4,z5]),(0,[z0,z6,z2,z3,z186,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z187]),(0,[z0,z79,z6,z2,z3,z4,z188]),(0,[z189,z0,z6,z2,z3,z4,z5]),(0,[z190,z0,z6,z2,z3,z4,z5])],[(0,[z191,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z192,z3,z4,z5]),(0,[z193,z0,z6,z2,z3,z4,z5]),(0,[z194,z0,z6,z2,z3,z24,z5])],[(0,[z0,z6,z2,z3,z195,z4,z5]),(0,[z196,z0,z6,z2,z3,z4,z5]),(0,[z197,z0,z6,z2,z3,z4,z76]),(0,[z198,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z199,z4,z5]),(0,[z0,z6,z2,z3,z4,z148,z5])],[(1,[z200,z55,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z74,z5]),(0,[z0,z6,z2,z3,z4,z57,z163]),(0,[z0,z134,z2,z3,z88,z4,z5])],[(0,[z0,z6,z2,z176,z39,z4,z5]),(0,[z0,z6,z2,z39,z4,z80,z5]),(0,[z0,z6,z2,z4,z5,z201,z202])]],
   [[(0,[z200,z0,z6,z2,z3,z24,z5]),(0,[z0,z6,z2,z203,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z204]),(0,[z0,z6,z2,z3,z4,z5,z163]),(0,[z0,z6,z2,z205,z3,z4,z5]),(0,[z0,z6,z206,z2,z3,z28,z5]),(0,[z0,z6,z2,z207,z3,z4,z5])],[(0,[z0,z6,z2,z208,z3,z28,z5])],[(0,[z209,z0,z6,z2,z3,z4,z5]),(0,[z200,z6,z2,z117,z3,z4,z5]),(0,[z0,z210,z6,z2,z3,z4,z5]),(1,[z0,z6,z2,z3,z4,z137]),(0,[z0,z6,z2,z211,z3,z4,z5]),(0,[z0,z6,z166,z2,z3,z24,z5])],[(0,[z0,z6,z2,z3,z212,z4,z5]),(0,[z20,z0,z6,z2,z3,z24,z5]),(1,[z0,z47,z2,z3,z89,z5])],[(0,[z0,z6,z2,z3,z4,z5,z213]),(0,[z0,z70,z134,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z214]),(0,[z0,z6,z2,z215,z3,z4,z5]),(0,[z0,z6,z216,z2,z3,z4,z5])],[(0,[z197,z0,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z217,z4,z5]),(0,[z0,z6,z2,z218,z3,z4,z5]),(0,[z0,z219,z6,z2,z3,z24,z5]),(0,[z0,z6,z220,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z221,z28,z5])],[(0,[z98,z0,z6,z2,z3,z4,z137]),(0,[z0,z6,z2,z3,z222,z4,z5]),(0,[z0,z6,z2,z3,z223,z4,z5]),(1,[z0,z6,z16,z2,z145,z5])],[(0,[z23,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z39,z4,z5]),(0,[z0,z6,z2,z2,z3,z28,z5]),(0,[z0,z6,z224,z2,z3,z4,z5]),(0,[z0,z6,z16,z2,z3,z145,z5])]],
   [[(0,[z0,z6,z30,z2,z3,z4,z5]),(0,[z0,z6,z2,z176,z32,z4,z5]),(1,[z193,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z225,z5]),(0,[z0,z6,z2,z3,z4,z226,z5]),(1,[z0,z6,z2,z3,z4,z161])],[(0,[z0,z6,z227,z2,z3,z4,z5]),(1,[z0,z6,z2,z3,z228,z5]),(0,[z15,z0,z47,z6,z2,z3,z5]),(0,[z0,z229,z6,z2,z3,z4,z5]),(0,[z0,z6,z175,z2,z155,z4,z5]),(0,[z0,z6,z2,z3,z230,z4,z5]),(0,[z0,z6,z38,z2,z3,z4,z57])],[(0,[z0,z6,z2,z3,z4,z5,z231]),(0,[z0,z232,z6,z2,z3,z4,z5]),(0,[z15,z0,z6,z2,z3,z74,z5]),(0,[z0,z6,z2,z3,z4,z233,z5]),(0,[z0,z6,z2,z3,z135,z4,z5]),(0,[z0,z6,z175,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z234])],[(0,[z0,z6,z2,z3,z4,z4,z5]),(0,[z0,z6,z2,z3,z4,z235,z5]),(0,[z0,z6,z2,z3,z4,z236,z5]),(0,[z0,z6,z2,z3,z4,z5,z237]),(0,[z0,z6,z2,z3,z238,z148,z5])],[(0,[z0,z6,z2,z3,z239,z4,z5]),(0,[z0,z6,z240,z2,z3,z4,z5]),(0,[z0,z6,z2,z241,z3,z4,z5]),(0,[z0,z6,z2,z242,z3,z4,z5])],[(0,[z243,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z244,z2,z3,z4,z5]),(0,[z0,z245,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z146,z4,z80,z5]),(0,[z0,z6,z246,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z4,z148,z58])],[(0,[z0,z6,z2,z247,z3,z4,z5]),(0,[z0,z6,z2,z248,z3,z4,z5]),(0,[z0,z6,z2,z3,z249,z4,z5]),(1,[z0,z250,z2,z3,z28,z5]),(0,[z0,z6,z2,z251,z3,z4,z5]),(0,[z0,z6,z2,z3,z24,z145,z5]),(0,[z0,z252,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z253])]],
   [[(0,[z0,z254,z6,z2,z3,z4,z5]),(0,[z0,z250,z2,z3,z4,z28,z5])],[(0,[z255,z0,z6,z2,z3,z4,z5]),(0,[z179,z0,z6,z2,z3,z28,z5]),(1,[z0,z6,z2,z3,z256,z5]),(0,[z0,z6,z2,z3,z24,z148,z5])],[(0,[z0,z6,z66,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z257,z4,z5]),(0,[z258,z0,z6,z2,z3,z4,z5]),(0,[z0,z259,z6,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z4,z260,z5]),(0,[z0,z6,z261,z2,z3,z4,z5]),(0,[z0,z70,z6,z2,z3,z4,z5]),(0,[z0,z79,z2,z262,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z89,z5]),(0,[z0,z6,z2,z3,z217,z24,z5]),(0,[z0,z6,z2,z46,z3,z4,z96])],[(0,[z0,z6,z263,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z264,z5]),(0,[z0,z6,z2,z3,z24,z5,z163]),(0,[z0,z139,z6,z2,z3,z148,z5]),(1,[z179,z0,z2,z3,z4,z58]),(0,[z0,z6,z2,z3,z265,z4,z5])],[(0,[z0,z6,z2,z117,z3,z4,z5]),(0,[z0,z6,z2,z3,z39,z24,z5]),(0,[z266,z0,z6,z2,z3,z4,z76]),(0,[z267,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z268,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z96]),(0,[z269,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z270])],[(0,[z0,z6,z271,z2,z3,z28,z5])],[(0,[z98,z0,z1,z2,z3,z4,z5]),(0,[z15,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z272,z5]),(0,[z0,z6,z2,z3,z4,z5,z273]),(0,[z0,z6,z274,z2,z3,z4,z5]),(0,[z0,z139,z6,z271,z2,z3,z5]),(0,[z0,z2,z3,z4,z275,z28,z5])]],
   [[(0,[z0,z232,z6,z11,z2,z3,z5]),(0,[z0,z6,z276,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z277,z5]),(0,[z0,z6,z175,z2,z3,z24,z5]),(0,[z0,z6,z38,z2,z3,z238,z4])],[(1,[z0,z232,z6,z2,z3,z5]),(0,[z278,z0,z6,z2,z3,z4,z5]),(0,[z197,z0,z6,z2,z46,z3,z4]),(0,[z0,z6,z279,z2,z3,z4,z5]),(0,[z158,z0,z6,z2,z3,z280,z5]),(0,[z158,z0,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z281,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z221,z5]),(0,[z0,z6,z2,z3,z238,z4,z5])],[(0,[z10,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z282,z5]),(0,[z0,z6,z72,z2,z54,z4,z5])],[(0,[z6,z11,z2,z117,z3,z4,z5]),(0,[z0,z6,z283,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z284,z5]),(0,[z0,z6,z2,z285,z3,z4,z5]),(0,[z0,z6,z2,z3,z28,z286,z5]),(0,[z0,z6,z38,z2,z3,z4,z132]),(0,[z0,z6,z2,z3,z4,z287,z5])],[],[(0,[z0,z6,z2,z288,z3,z4,z5]),(0,[z0,z6,z2,z39,z155,z4,z5]),(0,[z0,z6,z2,z3,z4,z289,z5]),(0,[z266,z0,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z290,z4,z5]),(1,[z0,z6,z2,z3,z4,z291]),(0,[z0,z6,z2,z3,z292,z4,z5])],[(0,[z122,z0,z6,z2,z3,z4,z5]),(1,[z266,z6,z2,z3,z4,z76]),(0,[z0,z6,z2,z3,z293,z4,z5]),(0,[z0,z6,z294,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z112,z132]),(0,[z0,z6,z295,z2,z3,z4,z5]),(0,[z0,z6,z296,z2,z3,z4,z5]),(0,[z0,z6,z38,z271,z2,z3,z4])],[(0,[z31,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z262,z3,z297,z5]),(0,[z0,z298,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z299,z4,z5]),(0,[z0,z6,z2,z46,z3,z4,z80])]],
   [[(0,[z0,z6,z300,z2,z3,z4,z5]),(0,[z0,z301,z6,z2,z3,z4,z5]),(1,[z0,z6,z2,z3,z4,z188]),(0,[z0,z6,z2,z3,z28,z302,z5])],[(0,[z31,z6,z2,z3,z39,z4,z5]),(0,[z0,z6,z2,z3,z4,z303,z5]),(0,[z0,z6,z118,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z304]),(0,[z0,z6,z305,z2,z3,z4,z5]),(0,[z0,z6,z2,z176,z3,z28,z5]),(0,[z0,z6,z2,z3,z146,z4,z5])],[(0,[z0,z6,z306,z2,z3,z4,z5]),(0,[z0,z139,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z307,z3,z4,z5])],[(0,[z0,z6,z2,z117,z3,z24,z5]),(0,[z0,z6,z2,z308,z3,z4,z5]),(1,[z0,z6,z2,z3,z235,z5]),(0,[z0,z6,z63,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z275,z5])],[(0,[z0,z47,z55,z2,z3,z4,z5]),(1,[z0,z309,z2,z3,z4,z5]),(0,[z310,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z311,z3,z4,z5]),(0,[z0,z6,z312,z2,z3,z4,z5]),(0,[z0,z6,z175,z176,z3,z4,z5])],[(0,[z313,z0,z6,z2,z3,z4,z5]),(0,[z314,z0,z6,z2,z3,z4,z5]),(0,[z15,z0,z6,z2,z3,z24,z5]),(0,[z0,z127,z6,z2,z262,z4,z5])],[(0,[z0,z6,z2,z3,z4,z5,z315]),(0,[z0,z127,z6,z38,z2,z4,z5])],[(0,[z0,z6,z2,z3,z4,z286,z5]),(0,[z0,z6,z2,z3,z4,z316,z5]),(0,[z0,z6,z2,z3,z24,z89,z5]),(0,[z0,z6,z2,z317,z3,z4,z5]),(0,[z0,z6,z2,z3,z238,z24,z5]),(0,[z0,z318,z6,z2,z3,z4,z5])]],
   [[(0,[z152,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z319,z5]),(0,[z0,z6,z2,z3,z320,z4,z5]),(0,[z0,z6,z2,z3,z321,z4,z5]),(1,[z0,z6,z2,z3,z280,z5]),(0,[z0,z6,z2,z3,z155,z28,z5]),(0,[z0,z6,z322,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z323])],[(0,[z266,z6,z2,z3,z4,z76,z5]),(0,[z0,z6,z175,z2,z176,z4,z5]),(0,[z0,z6,z2,z3,z4,z324,z5]),(0,[z0,z6,z2,z4,z80,z5,z96])],[(0,[z179,z0,z11,z2,z3,z4,z5]),(0,[z0,z6,z2,z325,z3,z4,z5]),(0,[z0,z6,z326,z2,z3,z4,z5]),(1,[z15,z6,z2,z3,z34,z5]),(0,[z0,z6,z2,z3,z4,z327,z5]),(0,[z0,z139,z6,z2,z3,z89,z5]),(0,[z0,z6,z72,z2,z328,z4,z5]),(0,[z0,z6,z271,z2,z46,z3,z4])],[(0,[z0,z6,z2,z329,z3,z4,z5]),(0,[z0,z6,z2,z3,z28,z5,z132]),(0,[z0,z6,z2,z3,z4,z5,z330]),(0,[z0,z6,z331,z2,z3,z4,z5])],[(0,[z0,z6,z332,z2,z3,z4,z5]),(0,[z0,z6,z2,z333,z3,z4,z5]),(0,[z0,z6,z84,z3,z4,z28,z5]),(0,[z0,z6,z2,z3,z24,z5,z334]),(0,[z0,z6,z16,z2,z3,z146,z5]),(1,[z0,z6,z2,z3,z238,z148]),(0,[z0,z6,z2,z3,z4,z5,z335])],[(0,[z0,z6,z2,z3,z4,z336,z5]),(0,[z31,z0,z6,z2,z3,z24,z5]),(1,[z0,z6,z2,z192,z3,z5]),(0,[z197,z0,z6,z38,z2,z3,z4]),(0,[z0,z79,z6,z38,z2,z4,z5]),(0,[z0,z219,z6,z2,z3,z4,z112])],[(0,[z0,z11,z2,z3,z4,z5,z112]),(0,[z337,z0,z6,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z146,z24,z5])]],
   [[(0,[z0,z6,z2,z3,z28,z58,z5]),(0,[z0,z338,z6,z2,z3,z28,z5]),(1,[z0,z6,z72,z3,z4,z57]),(0,[z0,z339,z6,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z4,z340,z5]),(0,[z266,z0,z6,z2,z46,z3,z4]),(0,[z0,z6,z341,z2,z3,z4,z5]),(0,[z194,z0,z6,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z342,z4,z5]),(0,[z0,z6,z2,z3,z4,z343,z5]),(0,[z0,z6,z175,z2,z3,z4,z161]),(0,[z0,z6,z2,z3,z344,z4,z5])],[(0,[z0,z6,z2,z262,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z58,z202]),(0,[z0,z6,z2,z3,z238,z4,z148])],[(0,[z55,z6,z11,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z228,z5]),(0,[z158,z0,z6,z2,z3,z67,z5]),(0,[z0,z6,z2,z3,z345,z4,z5]),(0,[z0,z6,z346,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z201])],[(0,[z200,z0,z6,z2,z3,z4,z5]),(0,[z0,z55,z6,z2,z3,z4,z260]),(0,[z197,z266,z6,z2,z3,z4,z5]),(1,[z0,z6,z347,z2,z3,z5]),(0,[z0,z6,z348,z2,z3,z4,z5])],[(1,[z0,z6,z142,z2,z3,z4]),(0,[z152,z0,z6,z2,z3,z24,z5])],[(0,[z0,z6,z2,z3,z4,z349,z5]),(0,[z0,z350,z6,z2,z3,z4,z5]),(1,[z0,z6,z2,z247,z4,z5])]],
   [[(0,[z0,z6,z2,z3,z297,z4,z5])],[(0,[z351,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z154,z2,z3,z24,z5]),(0,[z0,z6,z352,z2,z3,z4,z5]),(0,[z0,z6,z353,z2,z3,z4,z5])],[(0,[z354,z0,z6,z2,z3,z4,z5]),(0,[z0,z355,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z356]),(0,[z0,z70,z6,z134,z3,z4,z5]),(0,[z0,z6,z357,z2,z3,z4,z5]),(0,[z0,z219,z6,z2,z3,z4,z5]),(1,[z0,z6,z2,z3,z358,z5]),(0,[z0,z6,z359,z2,z3,z4,z5]),(0,[z0,z6,z360,z2,z3,z4,z5])],[(1,[z0,z6,z2,z3,z4,z260]),(0,[z98,z0,z6,z2,z247,z4,z5]),(0,[z0,z6,z66,z2,z3,z228,z5]),(0,[z0,z6,z2,z3,z4,z361,z5]),(0,[z0,z6,z362,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z363,z4,z5]),(0,[z0,z6,z2,z3,z4,z364,z5]),(0,[z0,z6,z175,z2,z3,z256,z5]),(0,[z0,z6,z2,z3,z275,z28,z5]),(0,[z0,z6,z2,z3,z4,z365,z5]),(0,[z0,z6,z366,z2,z3,z4,z5])],[(0,[z0,z6,z11,z2,z3,z28,z5]),(1,[z0,z6,z2,z3,z367,z5]),(0,[z0,z6,z2,z3,z368,z4,z5]),(0,[z0,z6,z2,z3,z4,z256,z5])],[(0,[z0,z6,z369,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z370]),(0,[z0,z6,z2,z3,z4,z371,z5])],[(0,[z0,z6,z372,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z145,z5])],[(0,[z0,z6,z373,z2,z3,z4,z5]),(1,[z20,z6,z2,z3,z74,z5]),(0,[z374,z0,z6,z2,z3,z4,z5]),(0,[z0,z127,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z375,z5]),(0,[z0,z6,z2,z376,z3,z4,z5]),(0,[z0,z6,z271,z2,z3,z4,z202]),(0,[z0,z6,z377,z2,z3,z4,z5])]],
   [[(0,[z98,z0,z6,z2,z3,z367,z5]),(0,[z0,z6,z2,z3,z4,z378,z5]),(0,[z0,z6,z2,z3,z35,z5,z112]),(0,[z0,z6,z2,z3,z379,z28,z5]),(0,[z0,z380,z6,z2,z3,z4,z5])],[(0,[z0,z6,z134,z2,z3,z4,z5]),(1,[z0,z6,z2,z3,z103,z5])],[(0,[z381,z0,z6,z2,z3,z4,z5]),(1,[z0,z6,z2,z3,z382,z5]),(0,[z0,z6,z2,z383,z3,z4,z5]),(0,[z158,z0,z6,z2,z285,z4,z5]),(0,[z0,z6,z84,z63,z3,z4,z5]),(0,[z0,z6,z2,z3,z28,z384,z5]),(0,[z385,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z271,z2,z3,z5,z202])],[(0,[z197,z0,z6,z72,z2,z3,z4]),(1,[z0,z6,z2,z3,z67,z5]),(0,[z0,z6,z386,z2,z3,z4,z5]),(0,[z387,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z388]),(0,[z0,z6,z389,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z390,z4,z5]),(0,[z0,z6,z2,z3,z391,z4,z5]),(0,[z158,z0,z2,z3,z88,z4,z5]),(0,[z0,z392,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z328,z4,z5])],[(0,[z0,z6,z2,z3,z393,z4,z5]),(0,[z266,z0,z6,z38,z2,z3,z4]),(1,[z159,z6,z2,z3,z4,z5])],[(0,[z98,z0,z6,z2,z3,z382,z5]),(0,[z0,z6,z2,z32,z3,z28,z5]),(0,[z0,z79,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z5,z394]),(0,[z0,z395,z6,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z396,z4,z5]),(0,[z0,z6,z2,z3,z28,z28,z5])]],
   [[(0,[z0,z0,z6,z2,z3,z4,z5]),(0,[z0,z55,z2,z3,z4,z5,z112]),(0,[z0,z6,z359,z2,z3,z24,z5]),(0,[z0,z6,z2,z21,z3,z4,z5])],[(0,[z0,z6,z2,z3,z4,z5,z397]),(1,[z0,z6,z141,z2,z4,z5])],[(0,[z0,z6,z2,z398,z3,z4,z5]),(1,[z158,z0,z94,z3,z4,z5]),(0,[z0,z6,z2,z3,z368,z24,z5]),(0,[z0,z6,z2,z176,z262,z4,z5]),(0,[z0,z6,z2,z3,z28,z399,z5]),(0,[z0,z6,z2,z3,z400,z4,z5])],[(0,[z0,z6,z2,z3,z4,z76,z132]),(0,[z0,z219,z6,z2,z3,z4,z58]),(0,[z0,z6,z2,z3,z24,z5,z132])],[(1,[z31,z6,z2,z39,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z401]),(0,[z0,z6,z2,z3,z4,z57,z76]),(0,[z0,z6,z402,z2,z3,z4,z5]),(0,[z0,z6,z154,z3,z155,z4,z5])],[(0,[z0,z55,z2,z3,z88,z4,z5]),(0,[z403,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z404,z4,z5]),(0,[z0,z405,z6,z2,z3,z4,z5]),(0,[z0,z6,z406,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z407,z4,z5]),(0,[z0,z6,z2,z3,z88,z28,z5]),(0,[z0,z6,z166,z2,z3,z4,z57]),(1,[z0,z6,z2,z21,z146,z5])],[(0,[z408,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z134,z2,z3,z24,z5]),(0,[z23,z0,z6,z2,z3,z28,z5]),(0,[z0,z6,z72,z2,z3,z24,z5])]],
   [[(0,[z0,z6,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z409,z3,z4,z5]),(0,[z0,z6,z2,z3,z24,z58,z5]),(0,[z0,z6,z2,z3,z24,z5,z202])],[(0,[z0,z6,z410,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z411,z4,z5]),(0,[z0,z6,z87,z2,z3,z4,z5]),(0,[z158,z0,z6,z2,z3,z4,z412]),(1,[z0,z6,z2,z3,z396,z5]),(0,[z0,z6,z2,z413,z3,z4,z5])],[(0,[z414,z0,z6,z2,z3,z4,z5]),(0,[z0,z127,z6,z2,z368,z4,z5]),(0,[z0,z6,z2,z262,z3,z415,z5]),(0,[z0,z6,z2,z3,z4,z5,z416]),(0,[z0,z6,z417,z2,z3,z4,z5]),(0,[z418,z0,z6,z2,z3,z4,z5])],[(0,[z419,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z420,z3,z4,z5]),(0,[z158,z0,z70,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z280,z5]),(0,[z0,z6,z2,z421,z3,z4,z5]),(0,[z422,z0,z6,z2,z3,z4,z5]),(0,[z0,z47,z2,z3,z4,z89,z5]),(0,[z0,z6,z347,z2,z3,z5,z112]),(0,[z0,z6,z2,z3,z4,z423,z5])],[(0,[z0,z6,z424,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z425,z5]),(0,[z0,z6,z2,z46,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z5,z426]),(0,[z0,z6,z427,z2,z3,z4,z5])],[(0,[z428,z0,z6,z2,z3,z4,z5]),(0,[z429,z0,z6,z2,z3,z4,z5]),(0,[z6,z2,z3,z4,z76,z5,z163]),(0,[z0,z6,z430,z2,z3,z4,z5]),(0,[z431,z0,z6,z2,z3,z4,z5]),(0,[z0,z139,z6,z2,z3,z145,z5]),(0,[z0,z6,z2,z3,z4,z5,z432]),(0,[z0,z6,z84,z2,z3,z4,z5]),(0,[z0,z250,z6,z2,z3,z28,z5])],[(0,[z138,z0,z6,z2,z39,z4,z5]),(0,[z0,z6,z2,z3,z4,z399,z5]),(0,[z0,z6,z2,z3,z4,z433,z5]),(0,[z0,z434,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z435]),(0,[z0,z6,z2,z21,z3,z24,z5])],[(0,[z0,z6,z2,z436,z3,z4,z5]),(0,[z0,z6,z437,z2,z3,z4,z5]),(1,[z0,z6,z2,z3,z297,z5]),(0,[z0,z6,z2,z3,z4,z438,z5])]],
   [[(0,[z0,z6,z2,z439,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z440]),(0,[z0,z6,z124,z2,z3,z39,z5]),(0,[z0,z6,z441,z2,z3,z4,z5])],[(0,[z0,z6,z2,z94,z3,z4,z5])],[(0,[z0,z6,z66,z2,z3,z28,z5]),(0,[z442,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z3,z4,z57,z5,z132]),(0,[z0,z443,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z444,z5])],[(0,[z0,z6,z2,z32,z4,z145,z5]),(1,[z0,z6,z2,z51,z4,z5]),(0,[z15,z0,z309,z2,z3,z4,z5]),(0,[z266,z0,z6,z72,z2,z3,z4]),(0,[z0,z70,z6,z2,z3,z28,z5]),(1,[z0,z6,z2,z3,z4,z394]),(0,[z0,z47,z6,z2,z3,z24,z5]),(0,[z0,z6,z445,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z334])],[(0,[z15,z6,z2,z3,z34,z4,z5]),(0,[z446,z0,z6,z2,z3,z4,z5]),(0,[z0,z447,z6,z2,z3,z4,z5]),(0,[z0,z6,z448,z2,z3,z4,z5])],[(0,[z179,z0,z55,z2,z3,z4,z5]),(0,[z98,z0,z6,z66,z3,z4,z5]),(0,[z0,z6,z2,z368,z155,z4,z5])],[(0,[z449,z0,z6,z2,z3,z4,z5]),(0,[z152,z0,z6,z66,z3,z4,z5]),(1,[z0,z6,z2,z168,z3,z4])],[(0,[z450,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z451,z4,z5]),(0,[z0,z6,z452,z2,z3,z4,z5]),(0,[z138,z0,z6,z2,z32,z4,z5]),(0,[z0,z6,z38,z2,z3,z4,z112]),(0,[z0,z6,z16,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z453,z5]),(0,[z0,z6,z38,z16,z2,z4,z5])]],
   [[(0,[z0,z6,z2,z3,z454,z4,z5]),(0,[z138,z6,z2,z32,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z455,z5]),(0,[z0,z456,z6,z2,z3,z4,z5]),(0,[z0,z6,z72,z2,z3,z114,z5])],[(0,[z457,z0,z6,z2,z3,z4,z5])],[(0,[z10,z0,z6,z2,z3,z28,z5]),(0,[z458,z0,z6,z2,z3,z4,z5]),(1,[z0,z37,z6,z2,z3,z5]),(0,[z459,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z460,z3,z4,z5])],[(0,[z0,z6,z84,z2,z3,z24,z5]),(0,[z0,z461,z6,z2,z3,z4,z5])],[(0,[z0,z6,z462,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z24,z463,z5])],[(0,[z0,z55,z6,z2,z3,z28,z5]),(0,[z0,z47,z6,z2,z3,z88,z5]),(0,[z0,z6,z2,z3,z464,z4,z5]),(0,[z0,z6,z2,z3,z4,z358,z5])],[(0,[z0,z6,z2,z3,z367,z4,z5]),(1,[z0,z6,z124,z2,z3,z5]),(0,[z0,z6,z2,z3,z4,z112,z202]),(0,[z0,z6,z154,z175,z3,z4,z5]),(0,[z0,z6,z62,z2,z3,z28,z5]),(0,[z0,z6,z2,z46,z3,z4,z57])],[(0,[z0,z6,z30,z2,z117,z3,z4]),(0,[z0,z6,z465,z2,z3,z4,z5]),(0,[z0,z6,z2,z94,z3,z24,z5]),(0,[z0,z6,z2,z3,z24,z28,z5])]],
   [[(0,[z466,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z467,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z468]),(0,[z0,z6,z2,z3,z469,z4,z5]),(0,[z0,z6,z2,z470,z3,z4,z5])],[(0,[z0,z6,z2,z471,z3,z4,z5]),(1,[z138,z6,z2,z32,z4,z5]),(0,[z266,z0,z6,z2,z211,z4,z5]),(0,[z0,z6,z472,z2,z3,z4,z5])],[(0,[z0,z6,z2,z192,z3,z39,z5]),(0,[z0,z139,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z473,z4,z5]),(0,[z0,z6,z474,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z475,z5]),(0,[z0,z6,z476,z2,z3,z4,z5]),(0,[z477,z0,z6,z2,z3,z4,z5])],[(0,[z0,z6,z2,z478,z3,z4,z5]),(0,[z158,z0,z6,z94,z3,z4,z5]),(0,[z0,z6,z38,z2,z155,z4,z5]),(1,[z0,z6,z2,z3,z28,z5]),(0,[z0,z6,z63,z2,z3,z28,z5]),(0,[z0,z6,z2,z479,z3,z4,z5])],[(0,[z0,z6,z480,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z481]),(0,[z0,z6,z2,z3,z4,z291,z145]),(0,[z0,z6,z38,z2,z3,z4,z5])],[(0,[z482,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z382,z5]),(0,[z0,z6,z2,z3,z4,z483,z5]),(0,[z197,z0,z6,z2,z3,z4,z112]),(0,[z0,z6,z154,z2,z155,z4,z5])],[(0,[z0,z6,z2,z3,z4,z484,z5]),(0,[z0,z6,z154,z2,z3,z4,z5])],[(0,[z98,z0,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z5,z485]),(0,[z0,z6,z2,z3,z4,z486,z5]),(0,[z0,z79,z6,z2,z262,z4,z5]),(0,[z0,z6,z2,z487,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z302,z5])]],
   [[(0,[z0,z6,z2,z488,z3,z4,z5]),(0,[z20,z0,z6,z2,z51,z4,z5]),(0,[z0,z6,z489,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z490,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z491]),(0,[z0,z6,z492,z2,z3,z4,z5]),(0,[z493,z0,z6,z2,z3,z4,z5])],[(0,[z494,z0,z6,z2,z3,z4,z5]),(0,[z266,z0,z6,z2,z495,z4,z5]),(0,[z496,z0,z6,z2,z3,z4,z5])],[],[(0,[z0,z6,z2,z497,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z498,z5]),(0,[z0,z6,z2,z3,z4,z188,z5]),(0,[z0,z6,z2,z3,z4,z499,z5]),(0,[z0,z6,z2,z3,z28,z80,z5]),(0,[z0,z6,z2,z3,z28,z5,z202])],[(0,[z0,z70,z11,z2,z3,z4,z5]),(1,[z197,z6,z2,z3,z4,z163]),(0,[z500,z0,z6,z2,z3,z4,z5]),(0,[z501,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z502,z3,z4,z5]),(0,[z0,z6,z16,z2,z4,z145,z5]),(0,[z0,z6,z2,z3,z4,z5,z503]),(0,[z0,z6,z504,z2,z3,z4,z5])],[(0,[z0,z6,z2,z505,z3,z4,z5]),(0,[z0,z506,z6,z2,z3,z4,z5]),(0,[z197,z6,z2,z3,z4,z5,z163]),(0,[z0,z6,z2,z507,z3,z4,z5]),(0,[z0,z6,z508,z2,z3,z4,z5]),(0,[z0,z6,z206,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z509,z4,z5]),(0,[z0,z6,z510,z2,z3,z4,z5]),(0,[z0,z511,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z512,z5]),(0,[z0,z6,z2,z46,z3,z238,z4])],[(0,[z0,z11,z2,z3,z88,z4,z5]),(0,[z0,z513,z6,z2,z3,z4,z5]),(1,[z0,z6,z2,z4,z5,z201]),(0,[z0,z514,z6,z2,z3,z4,z5])],[(0,[z158,z0,z6,z2,z515,z4,z5]),(0,[z0,z6,z2,z176,z368,z4,z5]),(0,[z0,z6,z2,z176,z4,z80,z5]),(0,[z0,z6,z472,z2,z3,z24,z5]),(0,[z0,z6,z2,z3,z516,z4,z5])]],
   [[(0,[z0,z1,z6,z2,z3,z4,z5]),(0,[z0,z517,z6,z2,z3,z4,z5]),(0,[z138,z0,z6,z2,z3,z28,z5]),(0,[z158,z0,z6,z2,z3,z4,z378]),(0,[z0,z518,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z519,z4,z5]),(0,[z520,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z521,z5]),(0,[z0,z6,z2,z3,z522,z24,z5]),(0,[z0,z6,z2,z46,z3,z4,z132]),(0,[z523,z0,z6,z2,z3,z4,z5])],[(0,[z0,z6,z524,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z525,z5])],[(0,[z197,z0,z6,z2,z3,z4,z5]),(0,[z0,z526,z6,z2,z3,z4,z5]),(0,[z0,z139,z6,z2,z3,z146,z5]),(0,[z0,z6,z38,z2,z3,z24,z5]),(0,[z0,z6,z2,z3,z4,z5,z132]),(0,[z0,z6,z527,z2,z3,z4,z5])],[(0,[z10,z0,z11,z2,z3,z4,z5]),(0,[z0,z6,z2,z39,z4,z145,z5]),(0,[z528,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z89,z28,z5]),(0,[z0,z6,z2,z21,z3,z145,z5])],[(0,[z0,z6,z2,z2,z3,z4,z5])],[(0,[z200,z0,z6,z2,z3,z28,z5]),(1,[z0,z136,z2,z3,z4,z5]),(0,[z98,z0,z6,z117,z3,z4,z5]),(0,[z0,z6,z529,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z530,z5]),(0,[z0,z6,z2,z3,z495,z4,z5]),(0,[z0,z6,z38,z2,z3,z4,z58]),(1,[z0,z6,z2,z3,z531,z5]),(0,[z0,z6,z532,z2,z3,z4,z5]),(0,[z533,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z534,z5])],[(0,[z535,z0,z6,z2,z3,z4,z5])],[(0,[z536,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z537]),(0,[z0,z6,z2,z538,z3,z4,z5]),(0,[z0,z6,z539,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z540,z5]),(0,[z0,z6,z2,z3,z4,z58,z5]),(0,[z0,z6,z166,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z80,z5]),(0,[z0,z6,z2,z3,z4,z5,z202])]],
   [[(0,[z20,z0,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z541,z3,z4,z5]),(0,[z542,z0,z6,z2,z3,z4,z5]),(0,[z0,z47,z6,z2,z3,z145,z5]),(0,[z543,z0,z6,z2,z3,z4,z5]),(0,[z544,z0,z6,z2,z3,z4,z5])],[(0,[z98,z0,z136,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z545,z4,z5]),(0,[z546,z0,z6,z2,z3,z4,z5]),(0,[z0,z47,z134,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z24,z183,z5])],[(0,[z0,z47,z6,z2,z3,z148,z5]),(0,[z0,z219,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z547,z3,z4,z5]),(0,[z548,z0,z6,z2,z3,z4,z5])],[(0,[z10,z6,z11,z2,z3,z4,z5]),(0,[z0,z549,z6,z2,z3,z4,z5]),(1,[z0,z6,z2,z3,z4,z282]),(0,[z15,z20,z6,z2,z3,z4,z5]),(0,[z550,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z551,z3,z4,z5]),(0,[z0,z6,z63,z3,z24,z4,z5])],[(0,[z0,z6,z2,z3,z4,z552,z5]),(0,[z553,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z134,z2,z3,z235,z5]),(1,[z0,z250,z2,z3,z4,z5]),(0,[z0,z6,z72,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z4,z554,z5]),(0,[z266,z0,z6,z2,z3,z4,z112]),(0,[z0,z47,z6,z271,z2,z3,z5]),(0,[z0,z6,z2,z3,z4,z5,z555])],[(0,[z0,z6,z2,z3,z556,z4,z5]),(0,[z6,z2,z32,z3,z39,z4,z5]),(0,[z0,z557,z6,z2,z3,z4,z5]),(0,[z189,z0,z6,z2,z3,z28,z5]),(1,[z0,z6,z2,z328,z4,z5])],[(0,[z0,z6,z2,z3,z515,z4,z5])]],
   [[(0,[z197,z0,z6,z2,z3,z24,z5]),(0,[z0,z558,z6,z2,z3,z4,z5]),(0,[z559,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z560,z5])],[(0,[z0,z6,z2,z3,z561,z4,z5]),(0,[z0,z6,z2,z3,z562,z4,z5]),(1,[z0,z6,z2,z3,z4,z160]),(0,[z0,z6,z2,z3,z4,z563,z5]),(1,[z0,z139,z2,z3,z88,z5]),(0,[z0,z6,z2,z3,z4,z564,z5]),(1,[z0,z6,z84,z3,z28,z5]),(1,[z0,z6,z271,z2,z3,z202])],[(0,[z565,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z566,z5]),(1,[z0,z6,z2,z3,z415,z5]),(0,[z0,z6,z2,z2,z3,z24,z5]),(0,[z0,z6,z2,z3,z4,z567,z5])],[(0,[z197,z0,z6,z2,z3,z4,z58]),(1,[z0,z6,z2,z3,z135,z5]),(0,[z0,z6,z2,z3,z568,z4,z5]),(0,[z0,z6,z38,z2,z176,z4,z5]),(0,[z0,z6,z2,z3,z569,z4,z5]),(0,[z0,z6,z271,z2,z3,z4,z5])],[(0,[z570,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z571,z4,z5]),(0,[z0,z572,z6,z2,z3,z4,z5]),(0,[z573,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z574,z3,z24,z5])],[(0,[z0,z6,z2,z3,z4,z575,z5]),(0,[z0,z6,z2,z3,z4,z5,z576]),(0,[z0,z6,z2,z3,z34,z4,z5]),(0,[z197,z0,z157,z2,z3,z4,z5]),(0,[z0,z577,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z578,z3,z4,z5]),(0,[z579,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z154,z2,z176,z4,z5]),(1,[z0,z6,z2,z3,z569,z5]),(0,[z0,z6,z2,z580,z3,z4,z5])],[(0,[z0,z55,z6,z2,z3,z4,z537]),(0,[z0,z6,z2,z3,z4,z581,z5]),(0,[z158,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z412]),(0,[z0,z6,z2,z3,z4,z5,z582]),(0,[z0,z6,z72,z3,z4,z57,z5]),(0,[z0,z6,z583,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z584])],[(0,[z98,z152,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z585,z4,z5]),(0,[z0,z6,z2,z3,z24,z5,z112]),(0,[z0,z6,z2,z3,z24,z344,z5]),(1,[z0,z6,z2,z3,z586,z5]),(0,[z0,z6,z2,z3,z587,z4,z5])]],
   [[(0,[z0,z6,z142,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z28,z76,z5]),(0,[z0,z47,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z588,z3,z4,z5])],[(0,[z152,z6,z11,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z589,z4,z5]),(0,[z0,z6,z590,z2,z3,z4,z5]),(1,[z0,z6,z2,z3,z4,z564]),(0,[z0,z6,z2,z3,z4,z384,z5])],[(1,[z0,z6,z2,z3,z545,z5]),(0,[z591,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z39,z28,z5]),(0,[z266,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z592,z4,z5]),(0,[z0,z6,z593,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z24,z80,z5]),(0,[z0,z6,z2,z3,z4,z463,z5])],[(0,[z0,z6,z2,z3,z594,z4,z5]),(1,[z0,z6,z2,z3,z4,z537]),(1,[z0,z6,z2,z285,z4,z5]),(0,[z0,z134,z2,z94,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z595,z5]),(0,[z179,z0,z6,z2,z3,z24,z5]),(0,[z0,z6,z2,z3,z4,z379,z5]),(1,[z0,z6,z2,z46,z4,z80])],[(0,[z0,z6,z2,z3,z596,z4,z5]),(0,[z0,z127,z6,z2,z4,z80,z5]),(0,[z0,z6,z2,z597,z3,z4,z5]),(0,[z0,z139,z2,z3,z88,z4,z5]),(0,[z0,z6,z598,z2,z3,z4,z5]),(0,[z0,z6,z175,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z599,z4,z5])],[(0,[z200,z0,z11,z2,z3,z4,z5]),(0,[z600,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z601,z4,z5]),(0,[z0,z6,z2,z176,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z28,z5])],[(0,[z0,z6,z2,z3,z50,z4,z5]),(0,[z158,z0,z2,z94,z3,z4,z5]),(0,[z179,z0,z6,z2,z3,z4,z58]),(0,[z0,z6,z2,z3,z602,z4,z5])]],
   [[(0,[z603,z0,z6,z2,z3,z4,z5]),(0,[z0,z47,z6,z2,z3,z89,z5]),(0,[z604,z0,z6,z2,z3,z4,z5])],[(0,[z0,z6,z271,z2,z3,z24,z5]),(0,[z0,z6,z2,z3,z605,z4,z5])],[(0,[z0,z6,z2,z3,z4,z606,z5]),(0,[z0,z607,z6,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z58,z5,z112]),(0,[z0,z6,z2,z3,z24,z57,z5])],[(0,[z0,z6,z2,z3,z4,z608,z5]),(0,[z0,z79,z6,z2,z3,z4,z609]),(0,[z610,z0,z6,z2,z3,z4,z5]),(0,[z0,z577,z6,z2,z3,z24,z5])],[(0,[z0,z6,z2,z3,z4,z611,z5]),(0,[z612,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z32,z4,z80,z5]),(0,[z0,z6,z2,z3,z4,z613,z5]),(0,[z158,z0,z6,z2,z3,z24,z5]),(0,[z0,z6,z614,z2,z3,z4,z5]),(0,[z0,z79,z6,z2,z368,z4,z5]),(0,[z0,z6,z154,z2,z3,z396,z5]),(0,[z255,z0,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z615,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z291,z5]),(1,[z0,z6,z38,z2,z4,z96])],[(0,[z200,z152,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z616,z4,z5]),(0,[z0,z6,z18,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z155,z4,z5]),(0,[z0,z6,z2,z3,z617,z4,z5])],[(0,[z0,z618,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z3,z4,z5]),(0,[z0,z6,z2,z619,z3,z4,z5])],[(0,[z0,z55,z70,z2,z3,z4,z5]),(0,[z620,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z103,z4,z5])]],
   [[(0,[z0,z6,z2,z117,z3,z28,z5]),(0,[z20,z0,z139,z6,z2,z3,z5]),(0,[z0,z6,z2,z3,z621,z4,z5]),(0,[z266,z0,z6,z2,z3,z24,z5]),(0,[z0,z127,z2,z3,z368,z4,z5]),(0,[z0,z6,z347,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z531,z4,z5]),(0,[z0,z622,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z21,z3,z146,z5])],[(0,[z0,z6,z2,z3,z4,z5,z623]),(0,[z0,z6,z166,z2,z3,z569,z5])],[(1,[z0,z6,z2,z454,z4,z5]),(0,[z624,z0,z6,z2,z3,z4,z5]),(0,[z15,z0,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z163,z132]),(0,[z0,z6,z2,z3,z625,z4,z5]),(0,[z0,z6,z2,z3,z148,z5,z202])],[(0,[z0,z6,z626,z2,z3,z4,z5]),(0,[z266,z0,z6,z2,z3,z4,z58]),(1,[z0,z6,z2,z3,z4,z412]),(0,[z0,z6,z2,z627,z3,z4,z5]),(0,[z0,z6,z166,z2,z3,z586,z5]),(0,[z0,z6,z166,z2,z3,z4,z132])],[(0,[z10,z200,z6,z2,z3,z4,z5]),(0,[z0,z6,z628,z2,z3,z4,z5]),(0,[z0,z309,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z176,z3,z24,z5]),(0,[z0,z6,z3,z24,z4,z28,z5]),(0,[z0,z6,z2,z3,z238,z28,z5]),(1,[z0,z6,z166,z3,z4,z132])],[(0,[z197,z0,z6,z166,z2,z3,z4]),(0,[z0,z338,z6,z2,z3,z4,z5]),(0,[z0,z47,z6,z2,z3,z146,z5]),(0,[z0,z6,z2,z629,z3,z4,z5]),(0,[z0,z6,z271,z2,z3,z4,z148])],[(0,[z98,z0,z6,z2,z454,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z630]),(0,[z0,z6,z2,z3,z631,z4,z5])],[(0,[z0,z6,z632,z2,z3,z4,z5]),(0,[z0,z6,z633,z2,z3,z4,z5]),(0,[z0,z6,z2,z262,z155,z4,z5]),(0,[z0,z6,z175,z2,z3,z531,z5]),(0,[z0,z6,z166,z72,z3,z4,z5])]],
   [[(0,[z0,z6,z2,z3,z634,z4,z5]),(0,[z0,z6,z2,z262,z3,z4,z5]),(0,[z0,z219,z2,z3,z4,z5,z112])],[(0,[z158,z0,z47,z2,z3,z4,z5]),(0,[z0,z6,z2,z635,z3,z4,z5]),(1,[z0,z6,z2,z3,z35,z5])],[(0,[z636,z0,z6,z2,z3,z4,z5]),(0,[z31,z0,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z5,z637])],[(0,[z638,z0,z6,z2,z3,z4,z5]),(0,[z0,z639,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z609]),(0,[z0,z6,z176,z3,z155,z4,z5]),(0,[z0,z6,z2,z3,z155,z24,z5]),(0,[z0,z6,z640,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z641,z4,z5])],[(0,[z0,z6,z642,z2,z3,z4,z5]),(0,[z0,z643,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z146,z28,z5]),(0,[z0,z6,z2,z3,z24,z64,z5]),(0,[z0,z6,z2,z644,z3,z4,z5])],[(0,[z0,z6,z645,z2,z3,z4,z5]),(0,[z0,z159,z6,z2,z3,z4,z5]),(0,[z0,z70,z6,z94,z3,z4,z5]),(0,[z0,z2,z262,z3,z368,z4,z5]),(0,[z0,z6,z2,z3,z522,z4,z5])],[(0,[z10,z0,z55,z2,z3,z4,z5]),(0,[z0,z47,z11,z2,z3,z4,z5]),(0,[z0,z6,z646,z2,z3,z4,z5]),(0,[z0,z647,z6,z2,z3,z4,z5])],[(0,[z0,z6,z648,z2,z3,z4,z5]),(0,[z20,z0,z6,z16,z2,z3,z5]),(0,[z197,z0,z6,z2,z3,z4,z163]),(0,[z0,z6,z2,z155,z4,z80,z5]),(0,[z0,z6,z166,z3,z4,z5,z132])]],
   [[(0,[z0,z649,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z650,z3,z4,z5]),(0,[z0,z157,z6,z2,z3,z4,z5]),(0,[z0,z6,z651,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z24,z76,z5]),(0,[z0,z6,z652,z2,z3,z4,z5]),(0,[z0,z6,z653,z2,z3,z4,z5])],[(0,[z0,z6,z11,z2,z3,z4,z5]),(0,[z0,z6,z2,z21,z39,z4,z5]),(1,[z0,z118,z2,z3,z4,z5]),(1,[z0,z127,z2,z368,z4,z5])],[(0,[z0,z654,z6,z2,z3,z4,z5]),(0,[z0,z6,z655,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z656]),(0,[z0,z6,z2,z3,z28,z5,z112]),(0,[z0,z6,z2,z3,z4,z111,z5])],[(0,[z152,z0,z6,z2,z3,z28,z5]),(0,[z15,z0,z6,z2,z3,z34,z5]),(1,[z0,z2,z3,z4,z275,z5]),(0,[z657,z0,z6,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z4,z5,z658]),(0,[z0,z127,z6,z2,z3,z4,z5])],[(0,[z158,z0,z6,z134,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z415,z5]),(0,[z0,z6,z16,z2,z4,z80,z5]),(0,[z0,z6,z2,z3,z659,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z660])],[(0,[z0,z6,z661,z2,z3,z4,z5]),(0,[z158,z193,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z262,z3,z24,z5]),(0,[z0,z6,z662,z2,z3,z4,z5]),(0,[z0,z6,z154,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z663,z4,z5]),(0,[z0,z6,z664,z2,z3,z4,z5]),(0,[z0,z6,z38,z2,z3,z4,z96])],[(1,[z0,z6,z2,z211,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z665]),(0,[z179,z0,z219,z2,z3,z4,z5]),(0,[z666,z0,z6,z2,z3,z4,z5])]],
   [[(0,[z0,z6,z120,z2,z3,z4,z145])],[(0,[z667,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z668,z2,z3,z4,z5]),(0,[z669,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z208,z3,z4,z5]),(1,[z0,z6,z2,z54,z4,z5])],[(0,[z0,z6,z2,z32,z155,z4,z5]),(0,[z0,z6,z2,z21,z32,z4,z5]),(0,[z0,z670,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z586,z5])],[(0,[z0,z6,z2,z32,z3,z4,z5]),(0,[z0,z6,z2,z3,z24,z34,z5]),(0,[z0,z79,z6,z2,z3,z4,z5]),(0,[z0,z6,z175,z2,z3,z4,z564]),(0,[z0,z6,z2,z3,z28,z5,z234])],[(0,[z0,z6,z33,z2,z3,z39,z4]),(0,[z179,z0,z6,z2,z3,z4,z112]),(0,[z0,z6,z2,z3,z4,z57,z112]),(0,[z0,z6,z2,z46,z3,z4,z112]),(1,[z0,z6,z2,z3,z114,z5]),(0,[z0,z6,z2,z3,z4,z671,z5])],[(0,[z0,z6,z2,z3,z4,z672,z5]),(0,[z266,z0,z6,z166,z2,z3,z4]),(0,[z0,z6,z2,z3,z4,z673,z5]),(0,[z674,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z18,z2,z4,z5,z112]),(0,[z0,z6,z2,z3,z28,z57,z5]),(0,[z0,z6,z2,z3,z4,z675,z5]),(0,[z676,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z677]),(0,[z0,z6,z271,z2,z3,z238,z5])],[(0,[z0,z6,z678,z2,z3,z4,z5]),(0,[z197,z0,z87,z2,z3,z4,z5]),(0,[z0,z679,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z112])],[(0,[z0,z6,z11,z2,z3,z24,z5]),(1,[z0,z6,z2,z495,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z680]),(0,[z0,z6,z2,z3,z681,z4,z5])]],
   [[(0,[z682,z0,z6,z2,z3,z4,z5]),(1,[z0,z6,z2,z3,z4,z609]),(0,[z0,z6,z2,z3,z8,z28,z5]),(0,[z0,z6,z683,z2,z3,z4,z5])],[(0,[z152,z0,z6,z117,z3,z4,z5]),(1,[z152,z6,z66,z3,z4,z5]),(0,[z0,z6,z2,z684,z3,z4,z5]),(1,[z0,z219,z2,z3,z4,z112]),(0,[z0,z6,z2,z574,z3,z4,z5])],[(0,[z0,z6,z2,z3,z685,z4,z5]),(0,[z0,z6,z686,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z687]),(0,[z15,z0,z139,z6,z2,z3,z5]),(0,[z0,z127,z6,z2,z3,z24,z5]),(0,[z0,z6,z38,z2,z3,z4,z80])],[(0,[z0,z6,z2,z3,z88,z4,z5]),(0,[z0,z6,z2,z3,z4,z688,z5])],[(0,[z0,z6,z66,z2,z3,z545,z5]),(0,[z0,z6,z2,z3,z663,z24,z5]),(0,[z0,z689,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z690,z5])],[(1,[z0,z6,z120,z2,z3,z4])],[(0,[z0,z6,z2,z3,z28,z5,z96]),(0,[z0,z6,z2,z3,z4,z5,z691]),(0,[z0,z6,z692,z2,z3,z4,z5])],[(0,[z200,z55,z6,z2,z3,z4,z5]),(0,[z0,z6,z693,z2,z3,z4,z5]),(0,[z694,z0,z6,z2,z3,z4,z5]),(0,[z266,z0,z6,z2,z3,z4,z163]),(0,[z0,z6,z2,z3,z368,z28,z5]),(0,[z0,z6,z695,z2,z3,z4,z5])]],
   [[(0,[z0,z47,z6,z2,z3,z4,z394]),(0,[z0,z6,z154,z2,z3,z358,z5]),(0,[z0,z6,z696,z2,z3,z4,z5]),(0,[z0,z6,z697,z2,z3,z4,z5])],[(0,[z0,z11,z2,z94,z3,z4,z5]),(0,[z200,z0,z55,z2,z3,z4,z5]),(0,[z0,z6,z2,z32,z3,z24,z5]),(1,[z0,z6,z2,z515,z4,z5]),(0,[z0,z79,z6,z2,z3,z24,z5]),(0,[z179,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z57,z5]),(0,[z0,z6,z2,z46,z3,z4,z5])],[(0,[z98,z0,z6,z2,z3,z4,z282]),(0,[z0,z6,z2,z168,z3,z4,z5]),(1,[z0,z6,z2,z3,z4,z378]),(1,[z0,z79,z2,z262,z4,z5]),(0,[z0,z250,z6,z2,z3,z4,z5]),(0,[z0,z6,z38,z2,z46,z4,z5])],[(0,[z31,z0,z6,z2,z39,z4,z5]),(0,[z0,z6,z2,z3,z4,z5,z698]),(0,[z0,z6,z2,z3,z4,z5,z5]),(0,[z0,z6,z2,z3,z4,z699,z5]),(1,[z0,z2,z3,z275,z28,z5]),(1,[z0,z6,z3,z24,z28,z5]),(0,[z0,z6,z2,z21,z146,z4,z5])],[(0,[z0,z6,z2,z3,z74,z28,z5]),(1,[z0,z70,z134,z3,z4,z5]),(0,[z0,z6,z134,z2,z3,z28,z5]),(0,[z0,z6,z700,z2,z3,z4,z5]),(0,[z0,z6,z72,z2,z3,z28,z5]),(0,[z0,z6,z2,z146,z4,z145,z5])],[(0,[z0,z6,z2,z3,z4,z701,z5]),(0,[z702,z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z238,z4,z202])],[(0,[z703,z0,z6,z2,z3,z4,z5]),(0,[z6,z66,z2,z117,z3,z4,z5]),(0,[z0,z6,z704,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z212,z24,z5])],[(0,[z705,z0,z6,z2,z3,z4,z5]),(1,[z0,z6,z33,z2,z3,z4]),(0,[z0,z6,z2,z3,z24,z74,z5]),(0,[z0,z6,z2,z3,z706,z4,z5]),(0,[z0,z6,z141,z2,z4,z5,z202])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z6,z142,z2,z3,z28]),(0,[z0,z6,z2,z3,z707,z5]),(0,[z0,z6,z2,z3,z708,z5]),(0,[z20,z0,z250,z2,z3,z5]),(0,[z0,z709,z2,z3,z4,z5]),(0,[z0,z6,z3,z199,z28,z5]),(0,[z0,z6,z2,z710,z24,z5])],[(0,[z0,z6,z2,z3,z711,z5]),(0,[z198,z55,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z712,z5]),(0,[z0,z6,z2,z211,z4,z112]),(0,[z713,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z28,z714])],[(0,[z0,z6,z2,z3,z24,z5]),(0,[z0,z6,z2,z3,z715,z5]),(0,[z0,z6,z2,z3,z716,z5]),(0,[z0,z6,z717,z2,z3,z4]),(0,[z0,z6,z16,z120,z2,z4]),(0,[z0,z6,z2,z146,z718,z5])],[(0,[z0,z6,z719,z3,z4,z5]),(0,[z0,z87,z2,z3,z24,z5])],[(0,[z0,z6,z2,z3,z4,z720])],[(0,[z0,z6,z2,z3,z721,z5]),(0,[z20,z6,z2,z3,z183,z5]),(0,[z193,z6,z2,z515,z4,z5]),(0,[z0,z6,z2,z3,z4,z722])],[(0,[z0,z723,z6,z2,z3,z5]),(0,[z0,z6,z2,z3,z724,z5]),(0,[z0,z309,z2,z3,z28,z5]),(0,[z193,z6,z2,z3,z4,z378]),(0,[z0,z6,z154,z155,z4,z5]),(0,[z0,z725,z2,z3,z28,z5]),(0,[z0,z6,z2,z574,z663,z5]),(0,[z0,z6,z38,z2,z4,z726])],[(0,[z0,z157,z2,z3,z4,z5]),(0,[z0,z6,z727,z2,z3,z4]),(0,[z728,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z176,z4,z564])]],
   [[(0,[z152,z6,z306,z3,z4,z5]),(0,[z0,z6,z2,z3,z729,z5]),(0,[z138,z6,z2,z32,z28,z5]),(0,[z0,z127,z2,z368,z4,z5]),(0,[z194,z6,z2,z3,z212,z5])],[(0,[z200,z55,z2,z3,z4,z537]),(0,[z0,z6,z730,z2,z3,z5]),(0,[z0,z6,z2,z731,z4,z5]),(0,[z0,z2,z732,z3,z28,z5]),(0,[z0,z6,z141,z2,z238,z4])],[(0,[z0,z6,z2,z3,z733,z5]),(0,[z98,z6,z117,z3,z24,z5]),(0,[z0,z6,z632,z3,z28,z5]),(0,[z0,z2,z3,z4,z275,z5]),(0,[z0,z2,z3,z4,z734,z5])],[(0,[z0,z2,z3,z4,z735,z5]),(0,[z0,z6,z2,z3,z4,z736]),(0,[z6,z2,z3,z34,z737,z5]),(0,[z197,z6,z2,z3,z4,z738]),(0,[z0,z6,z2,z739,z4,z5])],[(0,[z0,z6,z2,z3,z4,z740]),(0,[z0,z741,z6,z2,z3,z5]),(0,[z0,z93,z2,z3,z88,z5]),(0,[z0,z6,z2,z3,z4,z742])],[(0,[z703,z11,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z743]),(0,[z266,z0,z6,z2,z54,z4]),(0,[z0,z6,z2,z3,z744,z5])],[(0,[z0,z6,z2,z211,z4,z5]),(0,[z0,z6,z2,z168,z495,z4]),(0,[z0,z745,z2,z3,z28,z5]),(0,[z0,z250,z2,z3,z145,z5]),(0,[z0,z6,z2,z718,z145,z5])],[(0,[z159,z2,z3,z88,z4,z5]),(0,[z0,z47,z2,z3,z235,z5])]],
   [[(0,[z459,z11,z2,z3,z4,z5]),(0,[z746,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z747]),(0,[z0,z6,z2,z54,z4,z5])],[(0,[z266,z6,z2,z495,z4,z76]),(0,[z0,z6,z2,z3,z4,z748])],[(0,[z0,z6,z2,z749,z4,z5]),(0,[z0,z6,z2,z3,z4,z750]),(0,[z158,z0,z94,z285,z4,z5])],[(0,[z0,z6,z2,z751,z4,z5]),(0,[z197,z6,z2,z3,z28,z163]),(0,[z0,z6,z593,z3,z24,z5]),(0,[z0,z6,z692,z176,z4,z5]),(0,[z0,z6,z2,z3,z114,z5])],[(0,[z0,z6,z347,z2,z46,z3]),(0,[z0,z6,z154,z155,z24,z5]),(0,[z0,z338,z2,z3,z275,z5]),(0,[z0,z6,z206,z2,z3,z234])],[(0,[z31,z6,z2,z749,z4,z5]),(0,[z0,z157,z2,z3,z24,z5]),(0,[z0,z6,z2,z752,z4,z5]),(0,[z0,z6,z753,z3,z4,z5])],[(0,[z0,z6,z2,z754,z4,z5]),(0,[z0,z6,z2,z3,z4,z755]),(0,[z0,z6,z2,z168,z3,z24]),(0,[z0,z6,z2,z495,z4,z5]),(0,[z0,z6,z2,z3,z4,z756]),(0,[z0,z127,z2,z368,z24,z5]),(0,[z0,z6,z2,z3,z28,z757]),(0,[z0,z6,z2,z758,z4,z5])],[(0,[z0,z47,z2,z3,z89,z5])]],
   [[(0,[z152,z6,z66,z3,z4,z5]),(0,[z0,z759,z2,z3,z4,z5]),(0,[z0,z6,z2,z454,z382,z5]),(0,[z0,z6,z38,z2,z4,z356]),(0,[z0,z309,z2,z3,z4,z760]),(0,[z0,z157,z2,z3,z4,z58]),(0,[z0,z6,z2,z3,z761,z5]),(0,[z0,z219,z2,z3,z4,z112]),(0,[z0,z6,z2,z3,z4,z762])],[(0,[z0,z373,z2,z3,z4,z112]),(0,[z0,z6,z2,z763,z4,z5]),(0,[z0,z6,z18,z347,z2,z5]),(0,[z0,z6,z2,z3,z256,z564]),(0,[z0,z6,z175,z176,z24,z5])],[(0,[z0,z6,z2,z764,z4,z5]),(0,[z0,z2,z3,z4,z765,z5]),(0,[z0,z6,z2,z766,z4,z5]),(0,[z0,z250,z2,z3,z4,z714]),(0,[z0,z6,z2,z24,z5,z767])],[(0,[z0,z768,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z769,z5]),(0,[z0,z6,z2,z3,z770,z5]),(0,[z0,z6,z3,z28,z156,z5])],[(0,[z193,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z4,z771,z537]),(0,[z0,z136,z2,z3,z28,z5]),(0,[z0,z6,z2,z211,z24,z5]),(0,[z0,z6,z2,z3,z772,z5]),(0,[z0,z6,z2,z24,z111,z5]),(0,[z0,z2,z3,z28,z5,z773])],[(0,[z0,z514,z2,z3,z4,z58]),(0,[z0,z6,z62,z2,z302,z5]),(0,[z0,z6,z72,z54,z4,z57])],[(0,[z98,z6,z117,z3,z4,z137]),(0,[z0,z6,z2,z3,z774,z5]),(0,[z0,z775,z6,z2,z3,z5]),(0,[z159,z70,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z776,z5]),(0,[z0,z777,z94,z3,z4,z5]),(0,[z0,z79,z2,z262,z4,z188])],[(0,[z0,z6,z778,z2,z3,z5]),(0,[z0,z6,z2,z211,z4,z58]),(0,[z0,z6,z2,z3,z4,z779]),(0,[z0,z6,z2,z3,z780,z5])]],
   [[(0,[z0,z6,z2,z3,z781,z5]),(0,[z0,z6,z2,z3,z782,z5]),(0,[z0,z6,z2,z783,z4,z5]),(0,[z0,z6,z2,z4,z784,z5]),(0,[z0,z6,z72,z3,z114,z57])],[(0,[z0,z6,z785,z2,z4,z5]),(0,[z0,z786,z2,z3,z4,z5]),(0,[z0,z6,z787,z2,z3,z4]),(0,[z158,z0,z94,z3,z4,z412]),(0,[z0,z6,z2,z3,z4,z788]),(0,[z0,z6,z244,z3,z24,z5]),(0,[z0,z6,z2,z3,z789,z5]),(0,[z790,z6,z2,z3,z4,z5]),(0,[z0,z6,z3,z28,z5,z660])],[(0,[z0,z232,z118,z2,z3,z5]),(0,[z0,z6,z2,z3,z28,z282]),(0,[z0,z6,z2,z3,z4,z791]),(0,[z0,z792,z6,z2,z3,z5]),(0,[z0,z6,z2,z3,z793,z5]),(0,[z0,z2,z3,z275,z28,z5]),(0,[z0,z6,z2,z28,z5,z794]),(0,[z0,z6,z615,z3,z24,z5])],[(0,[z0,z6,z2,z3,z4,z795]),(0,[z0,z796,z2,z3,z4,z5]),(0,[z266,z0,z6,z18,z2,z4]),(0,[z0,z70,z134,z3,z4,z5]),(0,[z0,z250,z2,z3,z280,z5]),(0,[z0,z6,z797,z2,z3,z5]),(0,[z0,z70,z134,z3,z235,z5]),(0,[z0,z6,z2,z3,z722,z202]),(0,[z0,z6,z2,z798,z4,z5])],[(0,[z0,z6,z2,z799,z4,z5]),(0,[z0,z6,z2,z3,z24,z137])],[(0,[z0,z6,z33,z124,z2,z3]),(0,[z0,z6,z2,z515,z280,z5]),(0,[z0,z6,z2,z3,z256,z5]),(0,[z0,z6,z154,z800,z4,z5]),(0,[z0,z6,z2,z328,z28,z5])],[(0,[z0,z6,z2,z3,z801,z5]),(0,[z0,z6,z2,z802,z4,z5]),(0,[z0,z6,z33,z2,z3,z4]),(0,[z197,z6,z2,z3,z4,z364]),(0,[z0,z6,z2,z3,z280,z378]),(0,[z0,z250,z2,z3,z399,z5]),(0,[z0,z6,z2,z574,z146,z5])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z6,z107,z3,z28,z5]),(0,[z0,z47,z2,z3,z275,z5]),(0,[z0,z2,z3,z4,z58,z734])]],
   [[(0,[z0,z6,z2,z168,z3,z28]),(0,[z0,z6,z2,z3,z4,z803]),(0,[z0,z804,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z805,z5]),(0,[z0,z6,z2,z3,z28,z160]),(0,[z806,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z807,z5]),(0,[z0,z6,z3,z4,z808,z132])],[(0,[z138,z6,z2,z749,z4,z5]),(0,[z266,z6,z2,z3,z4,z688]),(0,[z6,z2,z3,z4,z5,z809]),(0,[z0,z79,z2,z4,z444,z5]),(0,[z0,z219,z2,z3,z4,z734]),(0,[z0,z6,z347,z2,z111,z5])],[(0,[z0,z6,z2,z810,z4,z5]),(0,[z0,z6,z240,z3,z4,z132]),(0,[z193,z6,z2,z3,z24,z5]),(0,[z0,z219,z347,z2,z3,z112]),(0,[z0,z6,z2,z3,z24,z161]),(0,[z255,z6,z2,z3,z8,z5]),(1,[z0,z6,z2,z718,z5])],[(0,[z0,z6,z2,z3,z4,z811]),(0,[z0,z6,z812,z2,z3,z4]),(0,[z6,z2,z3,z4,z738,z163]),(1,[z0,z6,z800,z4,z5]),(0,[z0,z6,z2,z3,z813,z5]),(0,[z0,z6,z2,z4,z80,z73])],[(0,[z0,z814,z2,z3,z4,z5]),(0,[z0,z6,z815,z2,z3,z5]),(0,[z0,z816,z2,z3,z4,z5]),(0,[z0,z219,z2,z4,z111,z112]),(0,[z0,z6,z360,z155,z4,z5]),(0,[z0,z6,z176,z800,z4,z5])],[(0,[z546,z55,z2,z3,z4,z5]),(0,[z0,z318,z2,z3,z4,z112]),(0,[z0,z6,z2,z817,z4,z5]),(0,[z0,z6,z818,z2,z4,z5]),(0,[z0,z819,z2,z3,z4,z5])],[(0,[z31,z6,z2,z192,z39,z5]),(0,[z0,z6,z2,z3,z820,z5]),(0,[z0,z6,z2,z3,z821,z5]),(0,[z0,z6,z2,z4,z5,z794])],[(0,[z0,z822,z2,z3,z4,z5]),(0,[z0,z6,z2,z46,z495,z4]),(0,[z0,z6,z635,z3,z24,z5]),(0,[z0,z47,z2,z3,z823,z5]),(0,[z0,z6,z487,z3,z28,z5]),(0,[z0,z250,z2,z3,z4,z757])]],
   [[(0,[z0,z6,z2,z3,z28,z564]),(0,[z0,z6,z824,z2,z3,z5]),(0,[z0,z3,z24,z275,z28,z5]),(0,[z122,z6,z2,z3,z183,z5])],[(0,[z0,z6,z2,z247,z4,z282]),(0,[z0,z6,z2,z3,z825,z5]),(0,[z0,z6,z2,z3,z826,z5]),(0,[z0,z6,z2,z3,z4,z291])],[(0,[z0,z6,z2,z827,z4,z5]),(0,[z0,z6,z2,z828,z4,z5]),(0,[z98,z6,z829,z3,z4,z5]),(0,[z20,z6,z2,z3,z737,z5]),(0,[z266,z6,z2,z3,z4,z76]),(0,[z0,z6,z644,z3,z24,z5])],[(0,[z0,z6,z2,z285,z28,z5]),(0,[z0,z6,z2,z285,z280,z5]),(0,[z0,z6,z2,z3,z830,z5]),(0,[z0,z6,z2,z46,z28,z80]),(0,[z0,z250,z2,z3,z146,z5])],[(0,[z6,z814,z2,z3,z4,z5]),(0,[z0,z6,z831,z2,z4,z5]),(1,[z6,z2,z749,z4,z5]),(0,[z0,z6,z2,z3,z4,z188]),(0,[z0,z6,z832,z2,z3,z4]),(0,[z0,z6,z3,z800,z4,z5]),(0,[z0,z6,z2,z3,z221,z384]),(1,[z0,z6,z2,z3,z722])],[(0,[z0,z1,z2,z3,z24,z5])],[(0,[z0,z6,z2,z3,z367,z282]),(0,[z0,z6,z650,z3,z24,z5])],[(0,[z0,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z833,z5]),(0,[z0,z6,z2,z3,z4,z834]),(0,[z0,z6,z2,z3,z235,z5]),(0,[z0,z6,z2,z835,z4,z5]),(0,[z0,z6,z2,z3,z238,z722])]],
   [[(0,[z0,z87,z2,z3,z4,z5]),(0,[z0,z6,z38,z2,z321,z4]),(0,[z0,z6,z836,z2,z3,z4]),(0,[z0,z6,z2,z3,z4,z837]),(0,[z0,z6,z3,z28,z5,z253])],[(0,[z0,z6,z2,z3,z838,z5])],[(0,[z0,z6,z2,z839,z4,z5]),(0,[z6,z2,z829,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z840]),(0,[z0,z6,z2,z841,z4,z5]),(0,[z0,z6,z120,z2,z3,z24])],[(0,[z0,z6,z2,z3,z4,z842]),(0,[z0,z6,z843,z2,z50,z4]),(0,[z0,z6,z844,z2,z3,z4]),(0,[z0,z6,z38,z2,z28,z96])],[(0,[z152,z136,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z382,z282]),(0,[z0,z6,z175,z176,z256,z5])],[(0,[z10,z37,z11,z2,z3,z5]),(0,[z0,z6,z800,z155,z4,z5])],[(0,[z0,z845,z2,z3,z4,z5]),(0,[z846,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z328,z103,z5]),(0,[z0,z6,z2,z146,z5,z25])],[(0,[z0,z6,z2,z847,z4,z5]),(0,[z0,z6,z18,z2,z4,z57]),(0,[z0,z6,z2,z848,z28,z5]),(0,[z0,z250,z2,z3,z302,z5]),(0,[z0,z2,z3,z28,z849,z5]),(0,[z0,z6,z2,z3,z24,z291])]],
   [[(0,[z0,z850,z2,z3,z4,z5]),(0,[z266,z6,z2,z3,z24,z76]),(0,[z0,z6,z2,z4,z851,z5]),(0,[z0,z6,z38,z2,z265,z4])],[(0,[z0,z6,z2,z454,z28,z5]),(0,[z0,z6,z30,z2,z852,z4]),(0,[z0,z6,z332,z155,z4,z5])],[(0,[z15,z0,z250,z2,z3,z5]),(0,[z159,z6,z2,z515,z4,z5]),(0,[z0,z6,z2,z3,z280,z412]),(0,[z0,z6,z2,z3,z28,z412]),(0,[z0,z6,z2,z3,z24,z188]),(0,[z0,z6,z2,z3,z853,z5])],[(0,[z0,z6,z2,z854,z3,z5]),(0,[z0,z6,z2,z855,z3,z5]),(0,[z0,z856,z2,z3,z4,z5]),(0,[z0,z6,z38,z2,z495,z4]),(0,[z159,z6,z2,z3,z4,z378]),(0,[z0,z6,z166,z3,z28,z132])],[(0,[z0,z6,z2,z3,z857,z5]),(0,[z0,z6,z2,z858,z4,z5]),(0,[z0,z6,z2,z3,z859,z5]),(0,[z0,z6,z72,z3,z4,z57])],[(0,[z0,z6,z2,z3,z860,z5]),(0,[z98,z6,z142,z117,z3,z4])],[(0,[z0,z6,z2,z3,z4,z861]),(0,[z0,z6,z2,z3,z5,z862]),(0,[z0,z55,z2,z3,z4,z394]),(0,[z0,z863,z2,z3,z4,z5]),(0,[z548,z6,z2,z32,z4,z5]),(0,[z197,z6,z123,z2,z3,z4]),(0,[z0,z6,z2,z3,z864,z5]),(0,[z0,z6,z2,z865,z4,z5]),(0,[z0,z6,z38,z2,z4,z609])],[(0,[z0,z6,z866,z2,z3,z5]),(0,[z0,z867,z2,z3,z4,z5]),(0,[z0,z6,z2,z868,z4,z5]),(0,[z158,z0,z94,z515,z4,z5]),(0,[z869,z6,z2,z3,z4,z5]),(0,[z0,z139,z2,z3,z567,z5]),(0,[z0,z6,z2,z3,z4,z870]),(0,[z0,z6,z2,z3,z871,z5])]],
   [[(0,[z0,z6,z72,z126,z3,z4]),(0,[z0,z6,z2,z3,z4,z872]),(0,[z158,z0,z94,z3,z4,z378])],[(0,[z0,z6,z2,z3,z873,z5]),(0,[z0,z6,z2,z3,z4,z874]),(0,[z0,z1,z2,z3,z4,z137]),(0,[z0,z6,z347,z2,z3,z5]),(0,[z0,z6,z2,z3,z24,z842]),(0,[z0,z6,z2,z4,z5,z767]),(0,[z0,z6,z2,z3,z238,z475])],[(0,[z429,z11,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z875]),(0,[z0,z6,z3,z4,z57,z808]),(0,[z0,z6,z38,z2,z4,z481]),(0,[z0,z6,z2,z3,z876,z5])],[(0,[z0,z6,z2,z247,z4,z5]),(0,[z0,z6,z2,z4,z111,z5]),(0,[z0,z2,z3,z4,z849,z5])],[(0,[z0,z6,z2,z3,z877,z5]),(0,[z0,z6,z2,z3,z4,z878]),(0,[z20,z6,z2,z50,z74,z5]),(0,[z0,z6,z362,z3,z24,z5]),(0,[z266,z6,z2,z211,z4,z76]),(0,[z0,z6,z2,z3,z879,z5]),(0,[z0,z6,z880,z2,z4,z5]),(0,[z0,z6,z2,z881,z3,z5]),(0,[z0,z882,z2,z3,z4,z5]),(0,[z0,z6,z3,z4,z5,z808]),(0,[z0,z6,z2,z883,z4,z5])],[(0,[z0,z6,z2,z3,z884,z5]),(0,[z0,z139,z6,z120,z2,z3]),(0,[z0,z6,z2,z3,z256,z161]),(0,[z0,z6,z175,z800,z4,z5])],[(1,[z814,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z885,z5]),(0,[z158,z193,z94,z3,z4,z5]),(0,[z0,z6,z2,z285,z67,z5]),(0,[z886,z6,z2,z3,z4,z5]),(0,[z0,z6,z175,z176,z4,z5]),(0,[z0,z6,z2,z625,z4,z80]),(0,[z0,z6,z692,z3,z4,z57])],[(0,[z0,z6,z3,z585,z28,z5])]],
   [[(0,[z0,z6,z2,z3,z887,z5]),(0,[z0,z6,z2,z888,z4,z5]),(0,[z6,z2,z749,z39,z4,z5]),(0,[z0,z6,z2,z889,z50,z4]),(0,[z0,z118,z2,z3,z28,z5]),(0,[z159,z6,z2,z285,z4,z5]),(1,[z0,z777,z3,z4,z5]),(0,[z0,z127,z2,z368,z28,z5]),(1,[z0,z2,z3,z4,z734]),(0,[z0,z6,z141,z2,z4,z112]),(0,[z0,z6,z504,z3,z24,z5]),(0,[z0,z6,z2,z3,z890,z5])],[(0,[z0,z139,z118,z2,z3,z5]),(0,[z0,z6,z2,z3,z4,z891]),(0,[z892,z6,z2,z3,z4,z5]),(0,[z0,z6,z3,z24,z226,z5])],[(0,[z0,z6,z2,z3,z893,z5]),(0,[z15,z118,z2,z3,z34,z5]),(0,[z0,z6,z2,z894,z4,z5]),(0,[z0,z6,z2,z3,z895,z5]),(0,[z0,z6,z72,z3,z24,z57]),(0,[z0,z6,z141,z271,z2,z4])],[(0,[z0,z6,z2,z3,z896,z5]),(0,[z98,z6,z117,z247,z4,z5]),(0,[z20,z6,z2,z3,z74,z5]),(0,[z897,z0,z6,z2,z3,z5]),(0,[z0,z577,z2,z3,z344,z5]),(0,[z0,z6,z271,z2,z3,z81])],[(0,[z0,z6,z898,z2,z3,z4]),(0,[z0,z899,z2,z3,z4,z5])],[(0,[z200,z55,z2,z3,z4,z5]),(0,[z0,z6,z2,z454,z367,z5]),(0,[z0,z6,z326,z3,z28,z5]),(0,[z0,z79,z2,z262,z297,z5]),(0,[z0,z6,z2,z800,z4,z5]),(0,[z0,z6,z166,z3,z4,z808])],[(0,[z0,z6,z2,z900,z4,z5]),(0,[z0,z6,z2,z3,z382,z5]),(0,[z194,z6,z2,z3,z34,z5]),(0,[z0,z6,z2,z901,z4,z5])],[(0,[z0,z6,z3,z4,z902,z5]),(0,[z0,z47,z2,z3,z280,z5]),(0,[z0,z6,z2,z3,z823,z5])]],
   [[(0,[z98,z6,z117,z3,z367,z5]),(0,[z0,z903,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z904,z5]),(0,[z0,z6,z2,z54,z28,z5]),(0,[z0,z6,z16,z120,z2,z145])],[(0,[z0,z6,z2,z3,z4,z137]),(0,[z0,z6,z2,z247,z24,z5]),(0,[z0,z6,z2,z3,z4,z905])],[(0,[z11,z2,z184,z3,z4,z5]),(0,[z0,z6,z906,z2,z3,z5])],[(0,[z0,z6,z2,z3,z4,z907]),(0,[z0,z6,z2,z3,z464,z148]),(0,[z0,z6,z359,z2,z3,z334])],[(0,[z0,z6,z2,z3,z908,z5]),(0,[z0,z6,z2,z3,z4,z909]),(0,[z0,z6,z700,z155,z4,z5])],[(0,[z0,z6,z2,z3,z910,z5]),(0,[z0,z6,z2,z3,z911,z5]),(0,[z0,z6,z2,z3,z24,z260]),(0,[z0,z6,z2,z3,z912,z5]),(0,[z0,z6,z2,z3,z67,z412]),(0,[z0,z6,z2,z3,z4,z913]),(0,[z0,z6,z16,z2,z145,z5]),(0,[z0,z6,z141,z2,z4,z5])],[(0,[z98,z6,z117,z3,z382,z5]),(0,[z15,z447,z6,z2,z3,z5]),(0,[z0,z6,z2,z495,z28,z5]),(0,[z158,z0,z94,z3,z4,z5]),(0,[z179,z0,z2,z3,z4,z734])],[(0,[z31,z6,z2,z168,z39,z4]),(0,[z0,z6,z2,z3,z5,z914]),(0,[z266,z6,z2,z588,z3,z4]),(0,[z159,z6,z2,z3,z4,z412]),(0,[z0,z6,z2,z3,z28,z609]),(0,[z0,z6,z2,z3,z4,z161]),(0,[z0,z6,z2,z3,z221,z148]),(0,[z0,z6,z2,z3,z522,z463])]],
   [[(0,[z0,z6,z2,z3,z228,z5]),(0,[z152,z6,z66,z3,z28,z5]),(0,[z0,z219,z2,z3,z28,z112]),(0,[z0,z6,z2,z3,z915,z5]),(0,[z0,z6,z154,z155,z358,z5]),(0,[z0,z6,z2,z3,z28,z762]),(0,[z0,z6,z2,z3,z916,z5])],[(0,[z458,z6,z117,z3,z4,z5]),(0,[z0,z6,z2,z4,z5,z917]),(0,[z0,z250,z2,z3,z384,z5]),(0,[z0,z6,z38,z2,z4,z691])],[(0,[z638,z11,z2,z3,z4,z5]),(0,[z0,z157,z2,z3,z4,z260]),(0,[z0,z6,z3,z24,z41,z5]),(0,[z918,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z21,z146,z5])],[(0,[z200,z55,z2,z3,z24,z5]),(0,[z0,z6,z166,z125,z3,z4]),(0,[z0,z6,z347,z2,z3,z148]),(1,[z0,z6,z3,z919,z5])],[(0,[z0,z6,z2,z3,z920,z5]),(0,[z193,z6,z2,z3,z280,z5]),(0,[z0,z250,z2,z3,z379,z5])],[(0,[z0,z6,z2,z921,z4,z5]),(0,[z200,z654,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z396,z5]),(0,[z0,z6,z166,z3,z569,z132])],[(0,[z0,z174,z2,z368,z4,z5]),(0,[z0,z6,z2,z4,z922,z5]),(0,[z0,z6,z2,z3,z923,z5]),(0,[z0,z924,z2,z3,z28,z5]),(0,[z0,z250,z2,z3,z28,z5])],[(0,[z31,z6,z124,z2,z39,z5]),(0,[z0,z6,z2,z925,z4,z5]),(0,[z266,z6,z2,z3,z4,z738]),(0,[z159,z6,z2,z3,z24,z5]),(0,[z0,z2,z777,z3,z4,z5]),(0,[z0,z6,z166,z3,z586,z132])]],
   [[(0,[z0,z6,z2,z4,z771,z5]),(0,[z0,z6,z2,z515,z28,z5]),(0,[z0,z6,z583,z3,z24,z5])],[(0,[z0,z6,z2,z3,z4,z926]),(0,[z266,z6,z353,z2,z3,z4]),(0,[z0,z6,z2,z3,z28,z378]),(0,[z0,z79,z2,z262,z28,z5])],[(0,[z0,z6,z2,z3,z4,z927]),(0,[z0,z6,z124,z2,z80,z5]),(0,[z0,z6,z843,z2,z3,z4]),(0,[z928,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z929,z5]),(0,[z0,z6,z2,z54,z4,z57]),(0,[z0,z6,z120,z2,z146,z4])],[(0,[z0,z6,z2,z3,z4,z930]),(0,[z0,z47,z82,z2,z3,z5]),(0,[z0,z6,z2,z285,z4,z412]),(0,[z0,z70,z134,z3,z28,z5]),(0,[z0,z6,z2,z3,z297,z5]),(0,[z0,z6,z2,z4,z931,z394]),(0,[z179,z0,z2,z3,z4,z58]),(0,[z0,z6,z2,z3,z932,z5]),(0,[z0,z2,z3,z4,z5,z773]),(0,[z0,z6,z141,z2,z24,z5])],[(0,[z0,z6,z2,z933,z4,z5]),(0,[z0,z6,z2,z3,z934,z5]),(0,[z0,z6,z120,z2,z32,z4]),(0,[z158,z0,z94,z3,z24,z5]),(0,[z0,z6,z2,z3,z935,z5]),(1,[z0,z2,z3,z823,z5]),(0,[z0,z167,z2,z3,z4,z58]),(0,[z0,z6,z38,z2,z4,z582])],[(0,[z0,z6,z2,z3,z936,z5]),(0,[z0,z6,z2,z247,z4,z137])],[(0,[z0,z232,z2,z3,z88,z5]),(0,[z0,z6,z937,z3,z4,z5]),(0,[z152,z6,z829,z3,z4,z5]),(0,[z31,z6,z2,z39,z24,z5]),(0,[z0,z6,z2,z3,z5,z938]),(0,[z0,z6,z141,z2,z4,z58]),(0,[z0,z939,z2,z3,z28,z5]),(0,[z0,z2,z3,z28,z940,z5])],[(0,[z0,z941,z6,z2,z3,z5]),(0,[z0,z6,z2,z51,z4,z5]),(0,[z20,z643,z6,z2,z3,z5]),(0,[z0,z6,z2,z3,z4,z394]),(0,[z0,z6,z448,z3,z28,z5])]],
   [[(0,[z10,z11,z2,z3,z28,z5]),(0,[z0,z232,z6,z2,z3,z5]),(0,[z0,z6,z18,z2,z28,z5]),(0,[z0,z6,z942,z2,z3,z28])],[(0,[z0,z6,z2,z943,z4,z5]),(0,[z0,z6,z944,z2,z3,z5]),(0,[z0,z134,z3,z4,z226,z5]),(0,[z0,z6,z2,z54,z103,z5])],[(0,[z0,z6,z2,z3,z4,z945]),(0,[z0,z6,z946,z2,z3,z4]),(0,[z0,z6,z947,z2,z3,z5]),(0,[z0,z6,z2,z3,z367,z137]),(0,[z6,z2,z3,z4,z5,z738]),(0,[z0,z6,z16,z2,z718,z5])],[(0,[z0,z6,z948,z2,z4,z5]),(0,[z0,z6,z2,z949,z4,z5]),(0,[z0,z950,z2,z3,z4,z5])],[(0,[z15,z6,z2,z3,z737,z5]),(0,[z159,z47,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z4,z951]),(0,[z0,z6,z2,z3,z952,z5]),(0,[z0,z6,z2,z4,z80,z726])],[(0,[z0,z6,z2,z3,z28,z537]),(0,[z0,z395,z2,z3,z4,z112]),(0,[z0,z6,z175,z176,z4,z161]),(0,[z0,z6,z2,z208,z379,z5]),(0,[z953,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z714])],[(0,[z0,z136,z2,z3,z4,z282]),(0,[z6,z829,z117,z3,z4,z5]),(0,[z0,z6,z33,z2,z155,z4]),(0,[z0,z6,z2,z3,z4,z954]),(0,[z0,z6,z154,z155,z396,z5]),(0,[z0,z822,z2,z3,z28,z5]),(0,[z0,z6,z2,z3,z24,z926])]],
   [[(0,[z0,z6,z2,z3,z382,z137]),(0,[z0,z955,z2,z3,z4,z5]),(0,[z0,z6,z2,z50,z28,z5]),(0,[z0,z6,z2,z311,z146,z5]),(0,[z0,z6,z2,z3,z4,z956]),(0,[z0,z957,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z4,z958]),(0,[z0,z6,z2,z3,z959,z5]),(0,[z0,z127,z2,z865,z4,z5]),(0,[z0,z139,z2,z3,z671,z5]),(0,[z0,z6,z2,z3,z960,z5]),(0,[z0,z6,z2,z3,z961,z5]),(0,[z179,z0,z2,z3,z24,z58])],[(0,[z0,z6,z2,z3,z962,z5]),(0,[z0,z6,z124,z2,z3,z5]),(0,[z0,z6,z2,z3,z963,z5]),(0,[z0,z6,z3,z516,z28,z5]),(0,[z0,z6,z63,z3,z919,z5])],[(0,[z0,z309,z2,z3,z4,z5]),(0,[z0,z964,z2,z3,z4,z5]),(0,[z0,z309,z2,z3,z4,z834]),(0,[z0,z6,z2,z3,z965,z5])],[(0,[z0,z2,z3,z966,z4,z5]),(0,[z0,z6,z2,z54,z4,z132]),(0,[z0,z6,z2,z46,z4,z121])],[(0,[z138,z6,z2,z32,z4,z5]),(0,[z0,z6,z2,z51,z24,z5]),(0,[z967,z6,z2,z3,z4,z5]),(0,[z968,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z24,z394]),(0,[z0,z6,z2,z3,z969,z5]),(0,[z0,z6,z970,z2,z28,z5])],[(0,[z0,z1,z2,z247,z4,z5]),(0,[z0,z6,z2,z3,z971,z5]),(0,[z0,z6,z2,z3,z972,z5]),(0,[z0,z2,z732,z3,z4,z5]),(0,[z0,z6,z2,z28,z5,z201]),(0,[z0,z6,z973,z2,z3,z4])],[(0,[z0,z6,z2,z3,z28,z5]),(0,[z0,z6,z2,z889,z3,z4]),(0,[z193,z6,z2,z3,z67,z5]),(0,[z0,z6,z2,z3,z280,z5]),(0,[z0,z6,z974,z2,z3,z4]),(0,[z0,z6,z2,z3,z718,z5])]],
   [[(0,[z0,z6,z2,z975,z4,z5]),(0,[z0,z976,z2,z3,z4,z5]),(0,[z0,z87,z2,z3,z28,z5]),(0,[z977,z6,z2,z3,z4,z5]),(0,[z978,z6,z2,z3,z4,z5]),(0,[z189,z0,z250,z2,z3,z5])],[(0,[z0,z6,z2,z3,z979,z5]),(0,[z136,z2,z117,z3,z4,z5]),(0,[z0,z980,z2,z3,z4,z5]),(0,[z15,z6,z2,z3,z34,z5]),(0,[z0,z6,z2,z4,z5,z981]),(0,[z0,z6,z598,z3,z4,z132]),(0,[z0,z6,z472,z2,z64,z5])],[(0,[z0,z6,z2,z3,z4,z982]),(0,[z0,z6,z2,z784,z28,z5]),(0,[z0,z983,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z4,z984]),(0,[z0,z1,z2,z3,z367,z5]),(0,[z0,z6,z985,z2,z3,z4]),(0,[z0,z6,z2,z515,z67,z5]),(0,[z0,z6,z2,z3,z986,z5]),(0,[z0,z250,z3,z24,z28,z5]),(0,[z0,z745,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z238,z148])],[(0,[z0,z6,z987,z2,z3,z4]),(0,[z0,z6,z2,z988,z3,z4]),(0,[z0,z6,z2,z192,z3,z5]),(0,[z0,z6,z2,z3,z67,z378]),(0,[z0,z6,z2,z3,z4,z989]),(0,[z0,z250,z84,z3,z28,z5])],[(0,[z0,z6,z2,z3,z990,z5]),(0,[z6,z2,z32,z749,z4,z5]),(0,[z158,z0,z777,z3,z4,z5]),(0,[z0,z6,z2,z3,z531,z564])],[(0,[z0,z991,z6,z2,z3,z5]),(0,[z6,z2,z3,z4,z76,z738]),(0,[z0,z6,z2,z3,z992,z5]),(0,[z0,z957,z2,z3,z24,z5]),(0,[z0,z6,z2,z3,z993,z5])],[(0,[z98,z6,z117,z3,z28,z5]),(0,[z152,z6,z66,z3,z545,z5]),(0,[z0,z6,z33,z2,z3,z24]),(0,[z0,z6,z2,z168,z4,z80])]],
   [[(0,[z0,z6,z2,z3,z994,z5]),(0,[z0,z6,z2,z995,z4,z5]),(0,[z0,z6,z2,z3,z996,z5]),(0,[z0,z79,z2,z262,z415,z5]),(0,[z0,z6,z2,z46,z4,z111]),(0,[z0,z6,z997,z2,z3,z4])],[(0,[z0,z1,z2,z3,z382,z5]),(0,[z0,z309,z2,z3,z24,z5]),(0,[z0,z6,z377,z3,z28,z5]),(0,[z0,z6,z206,z2,z3,z202])],[(0,[z267,z11,z2,z3,z4,z5]),(0,[z0,z998,z87,z2,z3,z5]),(0,[z0,z6,z2,z35,z111,z5]),(0,[z0,z6,z2,z4,z5,z201]),(0,[z0,z999,z2,z3,z4,z5])],[(0,[z138,z6,z2,z32,z24,z5]),(0,[z0,z70,z134,z3,z135,z5]),(0,[z0,z6,z2,z3,z4,z757]),(0,[z0,z1000,z2,z3,z4,z5]),(0,[z0,z6,z16,z2,z291,z145]),(0,[z0,z6,z2,z3,z1001,z5])],[(0,[z0,z6,z2,z3,z4,z1002]),(0,[z0,z6,z30,z2,z3,z24]),(0,[z0,z6,z2,z3,z1003,z5]),(0,[z0,z6,z141,z271,z2,z202])],[(0,[z0,z6,z2,z1004,z4,z5]),(0,[z0,z6,z142,z2,z3,z4]),(0,[z6,z66,z829,z3,z4,z5]),(0,[z0,z6,z2,z3,z919,z5])],[(0,[z0,z6,z124,z2,z50,z5]),(0,[z0,z6,z2,z3,z1005,z5]),(0,[z0,z47,z2,z3,z292,z5]),(0,[z0,z6,z2,z3,z1006,z5])],[(0,[z0,z6,z648,z3,z28,z5]),(0,[z0,z1007,z2,z3,z4,z5]),(0,[z0,z2,z3,z823,z4,z5]),(0,[z0,z6,z120,z2,z3,z28])]],
   [[(0,[z0,z1008,z2,z3,z4,z5]),(0,[z0,z1009,z6,z2,z3,z5])],[(0,[z0,z6,z2,z1010,z4,z5]),(0,[z0,z1011,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z1012,z5]),(0,[z0,z6,z2,z3,z358,z5]),(0,[z0,z6,z154,z155,z28,z5]),(0,[z0,z1013,z2,z3,z4,z5])],[(0,[z0,z6,z2,z3,z4,z260]),(0,[z0,z6,z2,z1014,z4,z5]),(0,[z0,z1015,z6,z2,z3,z5]),(0,[z0,z6,z1016,z2,z4,z5]),(0,[z0,z157,z2,z3,z28,z5]),(0,[z0,z6,z2,z285,z4,z378]),(0,[z0,z47,z2,z3,z89,z394])],[(0,[z0,z6,z1017,z3,z4,z5]),(0,[z0,z6,z2,z1018,z4,z5]),(0,[z0,z6,z2,z3,z367,z5]),(0,[z0,z6,z2,z21,z379,z5])],[(0,[z0,z6,z2,z3,z1019,z5]),(0,[z0,z2,z3,z865,z4,z5]),(0,[z0,z47,z6,z120,z2,z3]),(0,[z0,z6,z18,z2,z4,z132]),(0,[z0,z6,z2,z3,z4,z726])],[(0,[z0,z6,z1020,z2,z3,z4]),(0,[z0,z127,z474,z2,z4,z5]),(0,[z0,z6,z305,z3,z28,z5]),(0,[z0,z6,z2,z1021,z4,z5]),(0,[z0,z6,z2,z21,z718,z5])],[(0,[z0,z6,z2,z3,z1022,z5]),(0,[z0,z6,z2,z3,z4,z1023]),(0,[z0,z136,z2,z454,z4,z5]),(0,[z197,z6,z2,z3,z24,z163]),(0,[z0,z6,z2,z3,z1024,z5]),(0,[z0,z6,z175,z176,z28,z5])],[(0,[z0,z1025,z6,z2,z3,z5]),(0,[z0,z2,z3,z275,z235,z5]),(0,[z0,z6,z2,z3,z5,z1026]),(0,[z0,z6,z296,z3,z4,z57]),(0,[z0,z6,z2,z3,z1027,z5])]],
   [[(0,[z0,z6,z2,z3,z4,z1028]),(0,[z0,z6,z2,z3,z4,z1029]),(0,[z115,z6,z2,z3,z4,z76]),(0,[z0,z6,z2,z3,z103,z5])],[(0,[z0,z6,z1030,z2,z4,z5]),(0,[z98,z136,z117,z3,z4,z5]),(0,[z0,z6,z33,z2,z3,z28]),(0,[z0,z6,z2,z211,z28,z5])],[(0,[z814,z11,z2,z3,z4,z5]),(0,[z0,z6,z2,z1031,z4,z5]),(0,[z0,z6,z2,z3,z67,z5]),(0,[z0,z6,z2,z3,z1032,z5]),(0,[z0,z6,z2,z3,z1033,z5]),(0,[z0,z6,z2,z3,z24,z1034])],[(0,[z197,z157,z2,z3,z4,z163]),(0,[z0,z6,z1035,z3,z4,z5])],[(0,[z159,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z454,z4,z282]),(0,[z0,z950,z2,z3,z228,z5]),(0,[z0,z6,z38,z2,z4,z111]),(0,[z190,z0,z2,z3,z4,z58]),(0,[z1036,z6,z2,z3,z4,z5]),(0,[z0,z899,z2,z3,z28,z5])],[(0,[z0,z6,z2,z3,z4,z160]),(0,[z0,z139,z2,z3,z88,z5]),(0,[z0,z6,z84,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z1037])],[(0,[z0,z47,z2,z3,z606,z5]),(0,[z0,z6,z30,z2,z3,z28]),(0,[z0,z6,z2,z3,z4,z1038]),(0,[z0,z6,z2,z3,z1039,z5]),(0,[z0,z6,z124,z2,z168,z3]),(0,[z0,z6,z2,z3,z415,z5]),(1,[z0,z2,z865,z4,z5]),(0,[z0,z2,z262,z865,z4,z5]),(0,[z0,z6,z2,z24,z5,z201])],[(0,[z0,z136,z2,z3,z24,z5]),(0,[z98,z6,z117,z3,z4,z282]),(0,[z0,z6,z2,z3,z135,z5])]],
   [[(0,[z0,z6,z2,z1040,z3,z5]),(0,[z0,z6,z2,z515,z4,z412]),(0,[z0,z6,z2,z3,z4,z1041])],[(0,[z0,z6,z2,z3,z28,z137]),(0,[z0,z6,z2,z3,z4,z1042]),(0,[z0,z6,z1043,z3,z4,z5]),(0,[z0,z6,z2,z3,z148,z388]),(0,[z0,z6,z2,z3,z569,z5]),(0,[z0,z6,z331,z3,z24,z5])],[],[(0,[z0,z1044,z2,z3,z4,z5]),(0,[z31,z6,z2,z39,z4,z5]),(0,[z0,z6,z2,z3,z586,z5]),(0,[z0,z6,z271,z2,z201,z202])],[(0,[z0,z6,z1045,z2,z3,z4]),(0,[z0,z6,z2,z3,z4,z1046]),(0,[z0,z6,z2,z3,z148,z394])],[(0,[z0,z6,z2,z3,z4,z1047]),(0,[z0,z6,z2,z3,z24,z282]),(0,[z0,z6,z462,z3,z24,z5]),(0,[z0,z6,z2,z3,z1048,z5]),(0,[z159,z2,z94,z3,z4,z5]),(0,[z0,z250,z2,z3,z28,z714]),(0,[z0,z6,z72,z3,z103,z57])],[(0,[z0,z6,z2,z3,z545,z5]),(0,[z1049,z6,z2,z3,z4,z5]),(0,[z158,z0,z94,z3,z280,z5]),(0,[z0,z6,z2,z3,z1050,z5])],[(0,[z0,z6,z2,z247,z367,z5]),(0,[z0,z1051,z2,z3,z4,z5]),(0,[z193,z6,z2,z3,z28,z5]),(0,[z1052,z6,z2,z3,z4,z5]),(0,[z0,z6,z271,z2,z3,z394]),(0,[z0,z6,z2,z3,z28,z161]),(0,[z0,z6,z3,z24,z287,z5])]],
   [[(0,[z0,z6,z2,z1053,z3,z5]),(0,[z0,z6,z2,z3,z4,z1054]),(0,[z0,z6,z2,z192,z168,z3]),(0,[z0,z6,z2,z285,z4,z5]),(0,[z0,z6,z2,z328,z24,z5]),(0,[z0,z6,z2,z3,z1055,z5]),(0,[z0,z6,z2,z46,z4,z80])],[(0,[z0,z6,z2,z3,z4,z1056]),(0,[z0,z6,z2,z4,z1057,z5]),(0,[z0,z6,z2,z1058,z3,z5]),(0,[z0,z6,z2,z54,z114,z5])],[(0,[z0,z11,z347,z2,z3,z5]),(0,[z0,z2,z3,z4,z260,z112]),(0,[z150,z6,z2,z39,z4,z5]),(0,[z15,z6,z2,z3,z8,z5]),(0,[z0,z2,z3,z88,z235,z5]),(0,[z0,z2,z865,z368,z4,z5])],[(0,[z0,z6,z2,z1059,z4,z5]),(0,[z0,z998,z6,z2,z3,z5]),(0,[z0,z526,z2,z3,z4,z112]),(0,[z0,z6,z2,z3,z24,z160]),(0,[z0,z6,z84,z3,z919,z5])],[],[(0,[z0,z6,z2,z247,z382,z5]),(0,[z6,z2,z3,z28,z5,z1060])],[(0,[z0,z6,z33,z2,z192,z3]),(0,[z158,z0,z635,z3,z4,z5]),(0,[z0,z6,z18,z2,z35,z5]),(0,[z0,z6,z2,z1061,z4,z5])],[(0,[z0,z6,z2,z1062,z4,z5]),(0,[z544,z6,z2,z39,z4,z5]),(0,[z0,z1063,z6,z2,z3,z5])]],
   [[(0,[z0,z6,z1064,z3,z4,z5]),(0,[z200,z55,z2,z3,z4,z260]),(0,[z15,z6,z2,z580,z3,z5]),(0,[z0,z250,z2,z3,z88,z5]),(0,[z0,z6,z2,z1065,z4,z5]),(0,[z0,z6,z38,z2,z4,z96])],[(0,[z0,z6,z1066,z2,z4,z537]),(0,[z197,z0,z6,z2,z54,z4]),(0,[z0,z6,z2,z3,z1067,z5]),(0,[z0,z6,z38,z347,z2,z3])],[(0,[z0,z6,z2,z1068,z3,z4]),(0,[z0,z1,z2,z3,z28,z5]),(0,[z6,z2,z3,z737,z4,z5]),(0,[z0,z1069,z2,z3,z4,z5])],[(0,[z0,z136,z2,z3,z4,z137]),(0,[z0,z139,z6,z2,z50,z5]),(0,[z0,z6,z2,z3,z1070,z5]),(0,[z0,z6,z2,z3,z1071,z5]),(0,[z0,z6,z2,z3,z24,z564]),(0,[z6,z2,z1072,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z1073])],[(0,[z0,z6,z2,z1074,z3,z5]),(0,[z0,z6,z1075,z3,z4,z5]),(0,[z0,z6,z2,z3,z1076,z5]),(0,[z0,z2,z3,z735,z28,z5]),(0,[z0,z6,z2,z848,z4,z5])],[(0,[z0,z6,z2,z3,z1077,z5]),(0,[z179,z0,z2,z3,z4,z260]),(0,[z0,z6,z2,z3,z4,z1078]),(0,[z0,z6,z2,z3,z4,z1079]),(0,[z0,z6,z2,z168,z3,z4]),(0,[z0,z6,z2,z4,z80,z609])],[(0,[z200,z814,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z1080,z5]),(0,[z0,z6,z2,z285,z24,z5]),(0,[z0,z6,z2,z46,z24,z80])],[(0,[z0,z6,z2,z3,z4,z1081]),(0,[z0,z6,z2,z1082,z4,z5]),(0,[z0,z93,z2,z3,z217,z5])]],
   [[(0,[z0,z6,z2,z3,z1083,z5]),(0,[z20,z6,z346,z2,z3,z5]),(0,[z0,z6,z2,z1084,z3,z4]),(0,[z0,z84,z3,z275,z28,z5]),(0,[z0,z6,z2,z817,z28,z5])],[(0,[z0,z37,z6,z2,z3,z5]),(0,[z0,z1085,z2,z3,z4,z5]),(0,[z0,z6,z2,z328,z114,z5])],[(0,[z0,z1086,z6,z2,z3,z5]),(0,[z559,z6,z2,z3,z4,z163]),(0,[z0,z6,z1087,z2,z4,z5]),(0,[z0,z250,z2,z3,z28,z757]),(0,[z0,z1088,z2,z3,z4,z5])],[(0,[z0,z6,z2,z1089,z4,z5]),(0,[z0,z6,z2,z3,z1090,z5]),(0,[z0,z6,z2,z3,z5,z1091]),(0,[z0,z6,z2,z3,z1092,z5]),(0,[z0,z180,z2,z262,z4,z5]),(0,[z0,z6,z2,z3,z24,z1093])],[(0,[z0,z6,z1094,z3,z4,z5]),(0,[z10,z814,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z1095]),(0,[z0,z6,z1096,z2,z3,z4]),(0,[z0,z6,z38,z2,z4,z304]),(0,[z0,z6,z2,z3,z4,z1097]),(0,[z0,z250,z206,z2,z3,z5]),(0,[z0,z6,z2,z3,z28,z291]),(0,[z0,z6,z271,z2,z3,z334])],[(0,[z0,z6,z2,z1098,z3,z5]),(0,[z266,z6,z2,z3,z28,z76]),(0,[z0,z70,z777,z3,z4,z5]),(0,[z0,z6,z2,z3,z35,z5]),(0,[z0,z2,z3,z4,z940,z5]),(0,[z0,z6,z2,z24,z1057,z5])],[(0,[z55,z814,z2,z3,z4,z5]),(0,[z98,z6,z117,z454,z4,z5]),(0,[z269,z6,z2,z39,z4,z5]),(0,[z0,z6,z2,z3,z1099,z5]),(0,[z0,z79,z2,z262,z4,z609]),(0,[z0,z725,z2,z3,z4,z5]),(0,[z0,z6,z38,z2,z24,z96])],[(0,[z0,z6,z2,z3,z1100,z5]),(0,[z0,z6,z2,z3,z28,z188]),(0,[z0,z79,z2,z865,z4,z5]),(0,[z0,z6,z831,z2,z28,z5])]],
   [[(0,[z0,z6,z2,z3,z4,z1101]),(0,[z0,z6,z2,z3,z4,z1102]),(0,[z0,z6,z2,z3,z1103,z5]),(0,[z0,z47,z2,z3,z89,z160]),(0,[z0,z6,z2,z1104,z4,z5])],[(0,[z0,z6,z2,z4,z1105,z5]),(0,[z158,z0,z94,z3,z67,z5]),(0,[z0,z6,z2,z4,z5,z726]),(0,[z0,z6,z1106,z2,z3,z5])],[(0,[z0,z6,z16,z2,z50,z5]),(0,[z0,z6,z2,z1107,z4,z5]),(0,[z0,z47,z2,z3,z344,z5]),(0,[z255,z0,z250,z2,z3,z5])],[(0,[z0,z6,z829,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z1108]),(0,[z0,z6,z120,z2,z39,z4]),(0,[z676,z6,z2,z32,z4,z5])],[(0,[z0,z6,z2,z454,z24,z5]),(0,[z0,z6,z347,z2,z3,z394])],[(0,[z0,z118,z2,z3,z4,z5]),(0,[z15,z309,z2,z3,z34,z5]),(0,[z0,z6,z2,z3,z24,z412]),(0,[z0,z6,z2,z3,z5,z722])],[(0,[z0,z6,z2,z3,z737,z5]),(0,[z0,z219,z18,z2,z4,z112]),(0,[z0,z6,z166,z3,z24,z132]),(0,[z0,z6,z3,z24,z534,z5]),(0,[z0,z6,z38,z2,z4,z330])],[(0,[z197,z0,z6,z18,z2,z4]),(0,[z0,z6,z2,z515,z4,z378]),(0,[z0,z6,z880,z2,z4,z394]),(0,[z0,z6,z2,z3,z736,z28])]],
   [[(0,[z0,z232,z47,z2,z3,z5]),(0,[z0,z6,z2,z3,z4,z1109])],[(0,[z0,z47,z697,z2,z3,z5]),(0,[z0,z6,z38,z246,z2,z4])],[(0,[z0,z6,z2,z1110,z4,z5]),(0,[z0,z1,z2,z3,z4,z282]),(0,[z0,z6,z2,z1111,z4,z5]),(0,[z0,z6,z652,z3,z28,z5]),(0,[z0,z2,z3,z88,z823,z5])],[(0,[z0,z6,z2,z3,z4,z1112]),(0,[z535,z6,z2,z32,z4,z5]),(0,[z197,z6,z2,z3,z4,z163]),(0,[z0,z6,z2,z3,z4,z1113]),(0,[z0,z6,z2,z3,z1114,z5])],[(0,[z197,z87,z2,z3,z4,z163]),(0,[z158,z159,z94,z3,z4,z5]),(0,[z1115,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z1116,z5]),(0,[z0,z6,z427,z3,z24,z5])],[(0,[z0,z6,z2,z1117,z4,z5]),(0,[z0,z6,z2,z3,z4,z1118]),(0,[z0,z6,z1119,z2,z3,z5]),(0,[z0,z250,z2,z3,z148,z5])],[(0,[z0,z6,z2,z852,z4,z5]),(0,[z20,z6,z2,z51,z74,z5]),(1,[z6,z2,z3,z4,z738]),(0,[z0,z6,z2,z3,z1120,z5]),(0,[z0,z6,z2,z4,z5,z1121])],[(0,[z0,z6,z2,z3,z4,z1122]),(0,[z0,z1123,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z1124,z5]),(0,[z0,z2,z3,z1012,z228,z5]),(0,[z0,z6,z2,z3,z4,z1034]),(0,[z0,z6,z72,z3,z28,z57])]],
   [[(0,[z0,z11,z2,z3,z4,z394]),(0,[z0,z70,z410,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z1125]),(0,[z31,z6,z33,z2,z39,z4]),(0,[z0,z6,z2,z3,z4,z1126]),(0,[z193,z6,z2,z285,z4,z5]),(0,[z0,z6,z2,z3,z4,z1127]),(0,[z0,z250,z271,z2,z3,z5]),(0,[z0,z6,z2,z46,z4,z397])],[(0,[z0,z6,z2,z1128,z4,z5]),(0,[z0,z6,z110,z176,z4,z5])],[(0,[z0,z6,z30,z2,z802,z4]),(0,[z0,z6,z124,z2,z21,z5]),(0,[z0,z6,z38,z124,z2,z5]),(0,[z0,z6,z2,z1129,z4,z5])],[(0,[z0,z6,z2,z3,z1130,z4]),(0,[z0,z6,z1131,z2,z3,z5]),(0,[z0,z6,z1132,z2,z3,z5]),(0,[z189,z6,z2,z3,z74,z5]),(0,[z0,z118,z2,z3,z24,z5]),(0,[z0,z6,z2,z3,z4,z1133]),(0,[z0,z6,z3,z919,z28,z5]),(0,[z0,z1134,z2,z3,z4,z5]),(1,[z0,z6,z3,z4,z808])],[(0,[z0,z136,z2,z3,z4,z5]),(0,[z0,z1135,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z760]),(0,[z0,z6,z2,z3,z4,z609]),(0,[z0,z6,z2,z3,z531,z5])],[],[(0,[z0,z6,z2,z247,z28,z5]),(0,[z0,z6,z1136,z3,z4,z5]),(0,[z1137,z6,z2,z3,z4,z5]),(0,[z1138,z6,z2,z3,z4,z5]),(0,[z0,z6,z40,z3,z28,z5]),(0,[z0,z6,z2,z3,z24,z1109])],[(0,[z0,z6,z2,z3,z1139,z5]),(0,[z0,z87,z2,z46,z3,z4]),(0,[z0,z6,z2,z1140,z4,z5]),(0,[z0,z6,z2,z3,z1141,z5]),(0,[z0,z6,z2,z3,z1142,z5]),(0,[z0,z882,z2,z3,z28,z5])]],
   [[(0,[z0,z6,z2,z454,z4,z137]),(0,[z0,z6,z2,z3,z4,z1143]),(0,[z0,z6,z38,z2,z4,z370])],[(0,[z0,z6,z2,z3,z1144,z5]),(0,[z0,z6,z2,z3,z1145,z5]),(0,[z0,z6,z3,z4,z919,z5]),(0,[z0,z6,z120,z2,z3,z4])],[(0,[z0,z6,z2,z3,z28,z260]),(0,[z0,z6,z2,z3,z4,z282]),(0,[z1146,z6,z2,z3,z4,z5]),(0,[z0,z2,z3,z823,z89,z5])],[(0,[z458,z0,z94,z3,z4,z5]),(0,[z0,z6,z1147,z2,z3,z5]),(0,[z0,z924,z2,z3,z4,z5]),(0,[z0,z47,z118,z2,z3,z5]),(0,[z0,z250,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z1148]),(0,[z0,z2,z3,z24,z275,z5]),(0,[z0,z6,z2,z54,z24,z5])],[(0,[z0,z6,z2,z1149,z3,z4]),(0,[z0,z6,z2,z3,z1150,z5])],[(0,[z0,z6,z2,z3,z1151,z5]),(0,[z0,z55,z347,z2,z3,z5]),(0,[z0,z6,z661,z176,z4,z5]),(0,[z0,z6,z2,z515,z4,z5]),(0,[z0,z6,z2,z3,z1152,z5]),(0,[z0,z6,z2,z328,z4,z5])],[(0,[z0,z6,z2,z1153,z4,z5]),(0,[z0,z6,z2,z3,z4,z378]),(0,[z0,z6,z2,z3,z4,z1154]),(0,[z0,z79,z2,z262,z4,z5]),(0,[z0,z6,z683,z3,z4,z132])],[(0,[z0,z6,z2,z3,z4,z1155]),(0,[z0,z6,z2,z3,z1156,z5]),(0,[z197,z6,z492,z2,z3,z4]),(0,[z0,z6,z279,z3,z4,z57]),(0,[z193,z6,z2,z3,z4,z412]),(0,[z0,z6,z2,z3,z1157,z5]),(0,[z0,z6,z3,z24,z28,z5]),(0,[z0,z6,z973,z2,z3,z24])]],
   [[(0,[z200,z55,z2,z3,z28,z5]),(0,[z0,z6,z2,z1158,z4,z5]),(0,[z0,z139,z2,z3,z275,z5]),(0,[z0,z6,z2,z1129,z24,z5]),(0,[z0,z6,z271,z2,z3,z202])],[(0,[z0,z6,z2,z495,z24,z5]),(0,[z0,z6,z2,z1159,z4,z5]),(0,[z0,z6,z2,z3,z1160,z5]),(0,[z0,z6,z2,z3,z1161,z5]),(0,[z0,z219,z2,z3,z35,z112]),(0,[z0,z1134,z2,z3,z24,z5])],[(0,[z0,z6,z2,z3,z24,z609]),(0,[z0,z6,z38,z2,z641,z4])],[(0,[z98,z6,z30,z117,z3,z4]),(0,[z0,z939,z2,z3,z4,z5]),(0,[z152,z6,z66,z3,z24,z5]),(0,[z0,z250,z2,z3,z89,z5]),(0,[z0,z219,z2,z3,z24,z112]),(0,[z0,z6,z1162,z2,z3,z5])],[(0,[z0,z6,z86,z3,z28,z5]),(0,[z0,z6,z2,z4,z5,z1163]),(0,[z159,z6,z2,z3,z28,z5]),(0,[z159,z6,z2,z3,z280,z5]),(0,[z1164,z6,z2,z3,z4,z5]),(0,[z0,z6,z2,z763,z24,z5])],[(0,[z10,z11,z2,z3,z4,z5]),(1,[z6,z829,z3,z4,z5]),(0,[z0,z6,z2,z21,z50,z5]),(0,[z0,z6,z18,z2,z4,z5])],[(0,[z0,z6,z2,z1165,z3,z5]),(0,[z0,z6,z1166,z2,z3,z5]),(0,[z0,z6,z124,z2,z145,z5])],[(0,[z6,z2,z749,z3,z4,z5]),(0,[z0,z6,z2,z3,z1167,z5]),(0,[z0,z6,z2,z3,z1168,z5]),(0,[z1169,z0,z6,z2,z3,z4]),(0,[z0,z6,z2,z155,z4,z564])]],
   [[(0,[z0,z136,z2,z247,z4,z5]),(0,[z0,z6,z30,z2,z3,z4]),(0,[z0,z6,z1170,z3,z4,z5]),(1,[z6,z2,z3,z737,z5]),(0,[z6,z2,z3,z737,z74,z5]),(0,[z0,z6,z2,z4,z111,z609]),(0,[z0,z139,z2,z3,z823,z5]),(0,[z0,z6,z2,z3,z4,z564]),(0,[z0,z6,z141,z2,z28,z5])],[(0,[z0,z6,z2,z3,z1171,z5]),(0,[z0,z1,z2,z454,z4,z5]),(0,[z1172,z6,z2,z3,z4,z5]),(0,[z158,z0,z94,z3,z28,z5]),(0,[z0,z134,z777,z3,z4,z5]),(0,[z0,z6,z2,z3,z1173,z5]),(0,[z0,z250,z2,z3,z24,z5])],[(0,[z0,z6,z2,z21,z411,z5]),(0,[z0,z6,z2,z3,z1174,z5]),(0,[z0,z6,z2,z3,z1175,z5]),(0,[z0,z6,z72,z328,z4,z57])],[(0,[z0,z6,z2,z3,z4,z537]),(0,[z31,z6,z2,z39,z28,z5]),(0,[z0,z6,z2,z3,z4,z1176]),(0,[z0,z87,z38,z2,z3,z4]),(0,[z0,z6,z2,z515,z24,z5]),(0,[z0,z6,z2,z3,z1177,z5]),(0,[z0,z6,z175,z176,z531,z5]),(0,[z953,z6,z2,z3,z4,z5])],[(0,[z98,z1,z117,z3,z4,z5]),(0,[z0,z1178,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z24,z378]),(0,[z0,z79,z2,z262,z24,z5]),(0,[z0,z6,z62,z2,z145,z5]),(0,[z0,z6,z2,z4,z718,z5])],[(0,[z0,z136,z2,z3,z367,z5]),(0,[z0,z6,z2,z50,z4,z5]),(0,[z0,z6,z2,z3,z1179,z5]),(0,[z0,z6,z125,z3,z28,z5]),(0,[z0,z1180,z2,z3,z4,z5]),(0,[z918,z6,z2,z3,z28,z5]),(0,[z0,z6,z3,z24,z919,z5])],[(0,[z0,z6,z142,z2,z3,z24]),(0,[z0,z6,z2,z1181,z4,z5]),(0,[z6,z2,z3,z28,z1182,z5])],[(0,[z0,z1183,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z738]),(0,[z0,z6,z2,z3,z1184,z5]),(0,[z0,z6,z2,z3,z1185,z5]),(0,[z0,z6,z63,z3,z24,z5])]],
   [[(0,[z0,z6,z2,z4,z931,z5]),(0,[z0,z6,z38,z2,z4,z432]),(0,[z0,z6,z510,z3,z28,z5]),(0,[z0,z6,z2,z3,z4,z1093])],[(0,[z0,z6,z1186,z2,z3,z5]),(0,[z0,z6,z2,z4,z726,z96])],[(0,[z0,z6,z2,z710,z4,z5]),(0,[z0,z2,z3,z88,z280,z5]),(0,[z0,z6,z143,z3,z28,z5]),(0,[z0,z6,z2,z307,z145,z5]),(0,[z0,z6,z970,z2,z4,z5]),(0,[z0,z6,z2,z46,z4,z726])],[(0,[z10,z11,z2,z3,z24,z5]),(0,[z0,z136,z2,z3,z382,z5]),(0,[z0,z6,z2,z3,z1187,z5]),(0,[z0,z6,z18,z2,z24,z5]),(0,[z0,z250,z2,z3,z275,z5]),(0,[z0,z6,z72,z3,z4,z808])],[(0,[z10,z232,z11,z2,z3,z5]),(0,[z0,z1188,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z4,z1189])],[(0,[z0,z6,z2,z3,z4,z1190]),(0,[z0,z6,z2,z3,z1191,z5]),(0,[z149,z55,z2,z3,z4,z5]),(0,[z0,z6,z2,z1192,z4,z5]),(0,[z0,z6,z2,z1193,z4,z5]),(0,[z0,z6,z2,z21,z631,z5]),(0,[z0,z6,z2,z3,z1194,z5]),(0,[z0,z6,z1195,z2,z4,z5]),(0,[z1196,z6,z2,z3,z4,z5]),(0,[z0,z1197,z2,z3,z4,z5])],[(0,[z0,z6,z1198,z2,z4,z5]),(0,[z0,z6,z1199,z2,z4,z5]),(0,[z179,z0,z2,z3,z28,z58])],[(0,[z0,z6,z2,z1200,z4,z5]),(0,[z0,z6,z38,z2,z168,z4]),(0,[z0,z6,z2,z3,z148,z722])]],
   [[(0,[z0,z6,z777,z3,z4,z5]),(0,[z0,z6,z2,z3,z5,z1201]),(0,[z0,z6,z2,z3,z1202,z5]),(0,[z0,z6,z2,z3,z4,z734]),(0,[z0,z6,z818,z2,z24,z5])],[(0,[z0,z6,z2,z3,z24,z537]),(0,[z0,z6,z2,z454,z4,z5]),(0,[z0,z1203,z6,z2,z3,z5]),(0,[z0,z6,z2,z3,z4,z1204]),(0,[z0,z443,z2,z3,z4,z112])],[(0,[z0,z6,z2,z3,z4,z1205]),(0,[z0,z6,z33,z2,z176,z4]),(0,[z0,z47,z6,z2,z50,z5]),(0,[z0,z6,z2,z51,z28,z5]),(0,[z0,z157,z2,z3,z4,z112]),(0,[z0,z6,z2,z3,z4,z412]),(0,[z0,z6,z2,z1206,z4,z5]),(0,[z0,z6,z2,z3,z28,z394]),(0,[z6,z2,z3,z4,z1182,z5]),(0,[z0,z6,z16,z2,z64,z5]),(0,[z0,z6,z271,z2,z3,z722])],[(0,[z0,z6,z2,z50,z24,z5]),(0,[z0,z6,z2,z3,z4,z1207]),(0,[z0,z6,z997,z2,z3,z28]),(0,[z0,z6,z166,z3,z4,z132])],[(0,[z98,z6,z117,z3,z4,z5]),(0,[z0,z6,z90,z3,z28,z5]),(0,[z0,z6,z2,z3,z1208,z5]),(0,[z0,z6,z2,z28,z111,z5]),(0,[z0,z1209,z2,z3,z4,z5]),(0,[z0,z6,z2,z3,z531,z161]),(0,[z189,z6,z2,z3,z286,z5]),(0,[z6,z2,z3,z4,z5,z1060]),(1,[z0,z6,z2,z4,z726])],[(0,[z0,z6,z1066,z2,z4,z5]),(0,[z0,z6,z942,z2,z3,z4]),(0,[z0,z775,z87,z2,z3,z5]),(0,[z0,z2,z3,z4,z734,z112]),(0,[z0,z6,z347,z2,z3,z202]),(0,[z0,z6,z2,z3,z4,z808])],[(0,[z0,z6,z184,z3,z28,z5]),(0,[z152,z6,z66,z3,z228,z5]),(0,[z0,z6,z2,z1210,z4,z5]),(0,[z0,z6,z2,z3,z1211,z5]),(0,[z0,z6,z2,z3,z238,z463]),(0,[z0,z6,z16,z2,z81,z5])],[(0,[z159,z6,z2,z3,z67,z5]),(0,[z0,z6,z2,z3,z1212,z5]),(0,[z0,z6,z175,z176,z4,z564]),(0,[z0,z6,z2,z1213,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 528) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 528).take 529) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1057).take 189) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1246)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [528, 529, 189] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 109).take 119).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 228).take 28).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [109, 119, 28] = true :=
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

end PEqualNP.Outside.L_meta_38857

theorem PEqualNP.Outside.L_meta_38857 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209041632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209041632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38857.solve
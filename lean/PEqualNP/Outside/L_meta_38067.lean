import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38067

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
  Nat.testBit (4278124202 * 2 ^ 32 + 4276682376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x2a000402410d4155#64 ++ 0x02a000402410d415#64 ++ 0xfd880c1fc31f43ff#64 ++ 0x7fd880c1fc31f43f#64 : BitVec 256),
   (0x04043229046284a8#64 ++ 0x004043229046284a#64 ++ 0xdbd472690ce38cfe#64 ++ 0xedbd472690ce38cf#64 : BitVec 256),
   (0x4805828e10b4d0ce#64 ++ 0x14805828e10b4d0c#64 ++ 0xb727838e30fcf0cd#64 ++ 0xdb727838e30fcf0c#64 : BitVec 256),
   (0x103801502a002a00#64 ++ 0x6103801502a002a0#64 ++ 0x8ff803f03f00ff0b#64 ++ 0xf8ff803f03f00ff0#64 : BitVec 256),
   (0x607adc003fdb0000#64 ++ 0x4607adc003fdb000#64 ++ 0x7f7ffc003fff0007#64 ++ 0xc7f7ffc003fff000#64 : BitVec 256),
   (0x803f6bfd80000000#64 ++ 0x7803f6bfd8000000#64 ++ 0xff3fffffc0000000#64 ++ 0x3ff3fffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x8bd002600c008c0a 0xe8bd002600c008c0

def z1 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdbd472690ce38cfe 0xedbd472690ce38cf

def z2 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8ff803f03f00ff0b 0xf8ff803f03f00ff0

def z3 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfd880c1fc31f43ff 0x7fd880c1fc31f43f

def z4 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3427818e30fc70c5 0x13427818e30fc70c

def z5 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffc003fff0007 0xc7f7ffc003fff000

def z6 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3fffffc0000000 0x3ff3fffffc000000

def z7 : W := mkw 0x04001000046284a8 0x004001000046284a 0x00c000000ce38cfe 0xc00c000000ce38cf

def z8 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb727838e30fcf0cd 0xdb727838e30fcf0c

def z9 : W := mkw 0x803b49d480000000 0x7803b49d48000000 0x242b8d96c0000000 0x1242b8d96c000000

def z10 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x027003e03c00bc00 0x8027003e03c00bc0

def z11 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7007fc0000ff0004 0x07007fc0000ff000

def z12 : W := mkw 0x143c33792e62aea8 0x6143c33792e62aea 0xdbdc72790fe38ffe 0xedbdc72790fe38ff

def z13 : W := mkw 0x0805028e0024d0ce 0x10805028e0024d0c 0x8720038e3000f0c9 0xd8720038e3000f0c

def z14 : W := mkw 0x100000002a002a00 0x0100000002a002a0 0x00c000003f00ff0b 0xc00c000003f00ff0

def z15 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x00800000031f43ff 0x400800000031f43f

def z16 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x0237f3e000000000 0x00237f3e00000000

def z17 : W := mkw 0x604094003fdb0000 0x0604094003fdb000 0x004000003fff0007 0xc004000003fff000

def z18 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0ff800703f000f03 0xe0ff800703f000f0

def z19 : W := mkw 0x100001502a002a00 0x2100001502a002a0 0x80c003f03f00ff0b 0xf80c003f03f00ff0

def z20 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xfb17fe6fc0000000 0x2fb17fe6fc000000

def z21 : W := mkw 0x2e04362b456fc5fd 0x02e04362b456fc5f 0xffdc7e7fcfffcfff 0xfffdc7e7fcfffcff

def z22 : W := mkw 0x0004222900000000 0x0000422290000000 0xff1c7e7fc0000000 0x3ff1c7e7fc000000

def z23 : W := mkw 0x143c33792e62aea8 0x6143c33792e62aea 0x8ffc73f03fe0ff0b 0xf8ffc73f03fe0ff0

def z24 : W := mkw 0x0800000200044044 0x0080000020004404 0xfd80000f001f40ff 0x7fd80000f001f40f

def z25 : W := mkw 0x04042229002084a8 0x004042229002084a 0x8080026900008cf8 0x28080026900008cf

def z26 : W := mkw 0x6a7acc027b9d4155 0x46a7acc027b9d415 0xfdab8c1ff31f43ff 0x7fdab8c1ff31f43f

def z27 : W := mkw 0x100000002a002a00 0x0100000002a002a0 0x87e003803f00ff0b 0xd87e003803f00ff0

def z28 : W := mkw 0x4801808610945046 0x1480180861094504 0xa7238386301cf009 0xda7238386301cf00

def z29 : W := mkw 0x2000040001090000 0x0200004000109000 0x24080c00031c0001 0x024080c00031c000

def z30 : W := mkw 0x0004020800208088 0x0000402080020808 0x9304020800e080cc 0xc9304020800e080c

def z31 : W := mkw 0x803b69f580000000 0x7803b69f58000000 0x6c3bfdf7c0000000 0x36c3bfdf7c000000

def z32 : W := mkw 0x0400302104420420 0x0040030210442042 0x48d070610c030c32 0x248d070610c030c3

def z33 : W := mkw 0x4801808610945046 0x1480180861094504 0x24238186301c7001 0x124238186301c700

def z34 : W := mkw 0x04043229046284a8 0x004043229046284a 0x50c470090ce38cfe 0xc50c470090ce38cf

def z35 : W := mkw 0x2200040041090111 0x0220004004109011 0x48880c11c3030332 0x248880c11c303033

def z36 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0x0227838030e0b000 0x80227838030e0b00

def z37 : W := mkw 0xaa3f6fffc10d4155 0x7aa3f6fffc10d415 0xffbfffffc31f43ff 0x7ffbfffffc31f43f

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0x0b5000000c000002 0xc0b5000000c00000

def z39 : W := mkw 0x607acc003b990000 0x4607acc003b99000 0x2f7b8c003f1c0003 0xc2f7b8c003f1c000

def z40 : W := mkw 0x0400202100000420 0x0040020210000042 0x0080006100000c30 0x20080006100000c3

def z41 : W := mkw 0x2e04362b456fc5fd 0x02e04362b456fc5f 0xfbd47e6fccff8cfe 0xefbd47e6fccff8cf

def z42 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x7007fc0fc0000000 0x07007fc0fc000000

def z43 : W := mkw 0x84077aad846284a8 0x184077aad846284a 0xfbd7fe6fcce38cfe 0xefbd7fe6fcce38cf

def z44 : W := mkw 0x0038015000000000 0x6003801500000000 0x8fb803f00300430b 0x78fb803f00300430

def z45 : W := mkw 0xc83febff90b4d0ce 0x7c83febff90b4d0c 0xff3ffffff0fcf0cd 0xfff3ffffff0fcf0c

def z46 : W := mkw 0x143c33792e62aea8 0x6143c33792e62aea 0xdffc73f93fe3ffff 0xfdffc73f93fe3fff

def z47 : W := mkw 0x0004222900000000 0x0000422290000000 0xdb14726900000000 0x2db1472690000000

def z48 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xfffffff03fffff0f 0xffffffff03fffff0

def z49 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3227838e30fcb0c4 0x83227838e30fcb0c

def z50 : W := mkw 0x3a0004026b0d6b55 0x03a0004026b0d6b5 0xfdc80c1fff1fffff 0xffdc80c1fff1ffff

def z51 : W := mkw 0x627adc007fdb0111 0x4627adc007fdb011 0x7ffffc11ffff0337 0xe7ffffc11ffff033

def z52 : W := mkw 0x6a4094027fdf4155 0x06a4094027fdf415 0x00c000003fff43ff 0xc00c000003fff43f

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd080c1fc0000000 0x3fd080c1fc000000

def z54 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xff2f8f9ff0fcf0cd 0xfff2f8f9ff0fcf0c

def z55 : W := mkw 0xc807eaaf90b4d0ce 0x1c807eaaf90b4d0c 0x7007fc0fc0fc00c4 0x07007fc0fc0fc00c

def z56 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x70000c0fc01f00f4 0x070000c0fc01f00f

def z57 : W := mkw 0x2000040001090000 0x0200004000109000 0x00000000031f0007 0x400000000031f000

def z58 : W := mkw 0x6444b6293ffb84a8 0x06444b6293ffb84a 0xdbd472693fff8cff 0xedbd472693fff8cf

def z59 : W := mkw 0x04001000046284a8 0x004001000046284a 0x0000000000e300f4 0x00000000000e300f

def z60 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xffffffffff00ff0b 0xfffffffffff00ff0

def z61 : W := mkw 0x8002682180000000 0x0800268218000000 0x40007c01c0000000 0x040007c01c000000

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0xd900000900000000 0x2d90000090000000

def z63 : W := mkw 0x0038015000000000 0x6003801500000000 0x0818007000000000 0x2081800700000000

def z64 : W := mkw 0x803f6bfdaa000000 0x7803f6bfdaa00000 0xff7fffffff000003 0xfff7fffffff00000

def z65 : W := mkw 0x803a697180000000 0x6803a69718000000 0x0010706000000000 0x0001070600000000

def z66 : W := mkw 0x487fda8e3ef6d0ce 0x5487fda8e3ef6d0c 0xb777f38e3cfcf0cd 0xdb777f38e3cfcf0c

def z67 : W := mkw 0x0004020800208088 0x0000402080020808 0x0204020000e08000 0x80204020000e0800

def z68 : W := mkw 0x647efe293ffb84a8 0x4647efe293ffb84a 0xfffffe693fff8cff 0xefffffe693fff8cf

def z69 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdff473e93ce3fcff 0xfdff473e93ce3fcf

def z70 : W := mkw 0x04043229046284a8 0x004043229046284a 0x02d472600ce38cfe 0xc02d472600ce38cf

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0xd9800009000300fe 0x6d9800009000300f

def z72 : W := mkw 0x707acd503b992a00 0x6707acd503b992a0 0x242b8d90331c7301 0x1242b8d90331c730

def z73 : W := mkw 0x307a5d502f4b2a00 0x6307a5d502f4b2a0 0x48d87c700f030f02 0x248d87c700f030f0

def z74 : W := mkw 0x003800002a000000 0x4003800002a00000 0x8ff800103f00430b 0xf8ff800103f00430

def z75 : W := mkw 0x6a008402519d4155 0x06a008402519d415 0xffaf8c1ff3ff43ff 0xfffaf8c1ff3ff43f

def z76 : W := mkw 0x204014002f4b0000 0x0204014002f4b000 0x004000000f030002 0x0004000000f03000

def z77 : W := mkw 0x880523ff8024d0ce 0x3880523ff8024d0c 0x800003ffc000f0c8 0x3800003ffc000f0c

def z78 : W := mkw 0x0004222900000000 0x0000422290000000 0xdbd472690c008c0a 0xedbd472690c008c0

def z79 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x263ffff6c0000000 0x1263ffff6c000000

def z80 : W := mkw 0x4000800010900000 0x0400080001090000 0x3727800030fc0005 0xc3727800030fc000

def z81 : W := mkw 0x0005028c00000000 0x10005028c0000000 0xb727838e00000000 0x1b727838e0000000

def z82 : W := mkw 0x800523fd80000000 0x3800523fd8000000 0x000003e000000000 0x0000003e00000000

def z83 : W := mkw 0x84077aad846284a8 0x184077aad846284a 0x7007fc0fc0e300f4 0x07007fc0fc0e300f

def z84 : W := mkw 0x607acc003b990000 0x4607acc003b99000 0x7f3ffc00331c0001 0x07f3ffc00331c000

def z85 : W := mkw 0x0000000000000000 0x0000000000000000 0x872003803000f009 0xd872003803000f00

def z86 : W := mkw 0xc83febff90b4d0ce 0x7c83febff90b4d0c 0xb737f3ee30fcf0cd 0xdb737f3ee30fcf0c

def z87 : W := mkw 0x6847de8e15ffd0ce 0x16847de8e15ffd0c 0x7007fc0e00ff00c4 0x07007fc0e00ff00c

def z88 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffbfffffc00300fe 0x7ffbfffffc00300f

def z89 : W := mkw 0x4800800210b4d0ce 0x04800800210b4d0c 0x0000000030fcf0cd 0xc0000000030fcf0c

def z90 : W := mkw 0x684094023fffd0ce 0x0684094023fffd0c 0x004000003ffff0cf 0xc004000003ffff0c

def z91 : W := mkw 0x0000100004420000 0x0000010000442000 0x5b5470000ce30006 0xc5b5470000ce3000

def z92 : W := mkw 0x4805a2af10b4d0ce 0x14805a2af10b4d0c 0xff37f3ef30fcf0cd 0xfff37f3ef30fcf0c

def z93 : W := mkw 0x0000000000000000 0x0000000000000000 0x8d8800100300430b 0x78d8800100300430

def z94 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdfdc72790fe3cfff 0xfdfdc72790fe3cff

def z95 : W := mkw 0x803a697180000000 0x6803a69718000000 0x48187c71c0000000 0x248187c71c000000

def z96 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x24080c16c31c4301 0x124080c16c31c430

def z97 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x04e801903f00ff0b 0xd04e801903f00ff0

def z98 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x08d800700f000f02 0x208d800700f000f0

def z99 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7727fc0030ff0005 0xc7727fc0030ff000

def z100 : W := mkw 0x3a3805526b0d6b55 0x63a3805526b0d6b5 0x8ff803f03f1fffff 0xf8ff803f03f1ffff

def z101 : W := mkw 0x0404322904420420 0x0040432290442042 0xdbd472690c030c32 0x2dbd472690c030c3

def z102 : W := mkw 0xc805a3ff90b4d0ce 0x3c805a3ff90b4d0c 0xb72783fff0fcf0cd 0xfb72783fff0fcf0c

def z103 : W := mkw 0x3a3805526b0d6b55 0x63a3805526b0d6b5 0xfff80fffff1fffff 0xffff80fffff1ffff

def z104 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3007800e00fc00c4 0x03007800e00fc00c

def z105 : W := mkw 0x303805502b092a00 0x6303805502b092a0 0xfff80ff03f1fff0f 0xffff80ff03f1fff0

def z106 : W := mkw 0x0000000000000000 0x0000000000000000 0x7d080c0000000000 0x07d080c000000000

def z107 : W := mkw 0x6a05868e51bdd1df 0x16a05868e51bdd1d 0xffaf8f9ff3fff3ff 0xfffaf8f9ff3fff3f

def z108 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xfd0ffc1fc0000000 0x3fd0ffc1fc000000

def z109 : W := mkw 0x0a00000240044155 0x00a0000024004415 0x8080001fc00043f8 0x38080001fc00043f

def z110 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x8d880010031f43ff 0x78d880010031f43f

def z111 : W := mkw 0x607894003fdb0000 0x4607894003fdb000 0x0f7800003fff0007 0xc0f7800003fff000

def z112 : W := mkw 0x0005028c00000000 0x10005028c0000000 0x0227838000000000 0x0022783800000000

def z113 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x7f3fffe000000000 0x07f3fffe00000000

def z114 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x02f003e03f00ff0b 0xc02f003e03f00ff0

def z115 : W := mkw 0x003f4a8c00000000 0x5003f4a8c0000000 0xff3fff8e00000000 0x1ff3fff8e0000000

def z116 : W := mkw 0x003801502a000000 0x6003801502a00000 0x8f7803f03f000003 0xf8f7803f03f00000

def z117 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xf9800c0fc01f00fe 0x6f9800c0fc01f00f

def z118 : W := mkw 0x843f7bfd846284a8 0x7843f7bfd846284a 0xffffffffcce38cfe 0xfffffffffcce38cf

def z119 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z120 : W := mkw 0x4801808610b4d0ce 0x14801808610b4d0c 0x2423818630fcf0cd 0xd2423818630fcf0c

def z121 : W := mkw 0x6446fe2915fb84a8 0x06446fe2915fb84a 0xfbd7fe690cff8cfe 0xefbd7fe690cff8cf

def z122 : W := mkw 0x4800800210b4d0ce 0x04800800210b4d0c 0x8720038030fcf0cd 0xd8720038030fcf0c

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0x8fa803903300f30b 0xf8fa803903300f30

def z124 : W := mkw 0x6a7adc027fdf4155 0x46a7adc027fdf415 0xfffffc1fffff43ff 0xffffffc1fffff43f

def z125 : W := mkw 0xe07ffffdbfdb0000 0x7e07ffffdbfdb000 0xff7fffffffff0007 0xfff7fffffffff000

def z126 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0428019033007301 0x1042801903300730

def z127 : W := mkw 0x003a580004420000 0x4003a58000442000 0x7f7ffc000ce30006 0xc7f7ffc000ce3000

def z128 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb507800e00fc40cd 0x5b507800e00fc40c

def z129 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xffa80f9ff31ff3ff 0xfffa80f9ff31ff3f

def z130 : W := mkw 0x2a380552410d4155 0x62a380552410d415 0xffb80fffc31f43ff 0x7ffb80fffc31f43f

def z131 : W := mkw 0x687adc023fffd0ce 0x4687adc023fffd0c 0x7f7ffc003ffff0cf 0xc7f7ffc003ffff0c

def z132 : W := mkw 0xaa3b4dd6c10d4155 0x7aa3b4dd6c10d415 0x242b8d96c31c4301 0x1242b8d96c31c430

def z133 : W := mkw 0xc03febfd90900000 0x7c03febfd9090000 0xff3ffffff0fc0005 0xfff3ffffff0fc000

def z134 : W := mkw 0x403ac80010900000 0x4403ac8001090000 0x7f3ffc0030fc0005 0xc7f3ffc0030fc000

def z135 : W := mkw 0x800523fd80000000 0x3800523fd8000000 0x800003ffc0000000 0x3800003ffc000000

def z136 : W := mkw 0x04001000046284a8 0x004001000046284a 0x5bd470000ce38cfe 0xc5bd470000ce38cf

def z137 : W := mkw 0xe07bddd4bfdb0000 0x7e07bddd4bfdb000 0x7f7ffd96ffff0007 0xd7f7ffd96ffff000

def z138 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x781ffc7fc0000000 0x2781ffc7fc000000

def z139 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xb737f3ee00000000 0x1b737f3ee0000000

def z140 : W := mkw 0x2000040001090000 0x0200004000109000 0x7d080c00031f0007 0x47d080c00031f000

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0x3727800000000000 0x0372780000000000

def z142 : W := mkw 0x04043229046284a8 0x004043229046284a 0x5004700900e300f4 0x05004700900e300f

def z143 : W := mkw 0x843f6bfd802084a8 0x7843f6bfd802084a 0xffbfffffc0008cf8 0x3ffbfffffc0008cf

def z144 : W := mkw 0x0000000000000000 0x0000000000000000 0x8080001000004308 0x3808000100000430

def z145 : W := mkw 0xba3f6fffeb0d6b55 0x7ba3f6fffeb0d6b5 0xffffffffff1fffff 0xfffffffffff1ffff

def z146 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7d0ffc0003ff0007 0x47d0ffc0003ff000

def z147 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xff7fff803ffff00f 0xdff7fff803ffff00

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0x898000000000000a 0x6898000000000000

def z149 : W := mkw 0x0800000200044044 0x0080000020004404 0xb720038e301cf0cd 0xdb720038e301cf0c

def z150 : W := mkw 0x3a0004026b0d6b55 0x03a0004026b0d6b5 0x00c000003f1fffff 0xc00c000003f1ffff

def z151 : W := mkw 0x1000015000002a00 0x21000015000002a0 0x808003f00000ff08 0x3808003f00000ff0

def z152 : W := mkw 0x6a42dc0255df4155 0x06a42dc0255df415 0xfd8ffc1fc3ff43ff 0x7fd8ffc1fc3ff43f

def z153 : W := mkw 0x903b49d4aa002a00 0x7903b49d4aa002a0 0x242b8d96f3007301 0x1242b8d96f300730

def z154 : W := mkw 0x4005828c10900000 0x14005828c1090000 0xb727838e30fc0005 0xdb727838e30fc000

def z155 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xfffffc093fff00ff 0xefffffc093fff00f

def z156 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x6c880c17c31f4333 0x36c880c17c31f433

def z157 : W := mkw 0x800101d480000000 0x3800101d48000000 0x00000196c0000000 0x100000196c000000

def z158 : W := mkw 0x407ad8003ed20000 0x4407ad8003ed2000 0x0277f0003ce00000 0x80277f0003ce0000

def z159 : W := mkw 0x607acc003b990000 0x4607acc003b99000 0x242b8c00331c0001 0x0242b8c00331c000

def z160 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0xb727838e30e0b000 0x9b727838e30e0b00

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x8ff003e03c00fc0b 0xf8ff003e03c00fc0

def z162 : W := mkw 0x840523fd802084a8 0x3840523fd802084a 0x808003ffc0008cf8 0x3808003ffc0008cf

def z163 : W := mkw 0x407ad8003ed20000 0x4407ad8003ed2000 0x3777f0003cfc0005 0xc3777f0003cfc000

def z164 : W := mkw 0x0038015000000000 0x6003801500000000 0x8f3803f000000000 0x38f3803f00000000

def z165 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdb14726900e300f4 0x2db14726900e300f

def z166 : W := mkw 0x0a00000240044155 0x00a0000024004415 0x00800000000043f8 0x000800000000043f

def z167 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xffffffffcf000f02 0x3ffffffffcf000f0

def z168 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x00000000001f00f4 0x000000000001f00f

def z169 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0x3727838030fcb005 0xc3727838030fcb00

def z170 : W := mkw 0x8a0523ffc0044155 0x38a0523ffc004415 0x808003ffc00043f8 0x3808003ffc00043f

def z171 : W := mkw 0x747eff793ffbaea8 0x6747eff793ffbaea 0xfffffff93fffffff 0xffffffff93ffffff

def z172 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7f7ffd903fff7307 0xd7f7ffd903fff730

def z173 : W := mkw 0x04043229046284a8 0x004043229046284a 0x025472600ce08c00 0x8025472600ce08c0

def z174 : W := mkw 0x0800000200044044 0x0080000020004404 0xbd88001e031c43cf 0x7bd88001e031c43c

def z175 : W := mkw 0x800523fd80000000 0x3800523fd8000000 0xfd080fffc0000000 0x3fd080fffc000000

def z176 : W := mkw 0x647afc213fdb0420 0x4647afc213fdb042 0x7ffffc613fff0c37 0xe7ffffc613fff0c3

def z177 : W := mkw 0x04043229046284a8 0x004043229046284a 0xd304720900e380fc 0xcd304720900e380f

def z178 : W := mkw 0xa23a6d71c1090111 0x6a23a6d71c109011 0x48987c71c3030332 0x248987c71c303033

def z179 : W := mkw 0x803f6bfd80208088 0x7803f6bfd8020808 0xff3fffffc0e080cc 0xfff3fffffc0e080c

def z180 : W := mkw 0x583d83de3ab4face 0x7583d83de3ab4fac 0xb77783ee3cfcfccd 0xdb77783ee3cfcfcc

def z181 : W := mkw 0xea3fefffd1bdd1df 0x7ea3fefffd1bdd1d 0xffbffffff3fff3ff 0xfffbffffff3fff3f

def z182 : W := mkw 0x207a5c002f4b0000 0x4207a5c002f4b000 0x48587c000f030002 0x048587c000f03000

def z183 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x742ffd9fc0000000 0x1742ffd9fc000000

def z184 : W := mkw 0x407ad8003ed20000 0x4407ad8003ed2000 0x0f7ff0003fe00003 0xc0f7ff0003fe0000

def z185 : W := mkw 0x0002480000000000 0x0000248000000000 0x7007fc0000000000 0x07007fc000000000

def z186 : W := mkw 0x5c3db3ff3ef6feee 0x75c3db3ff3ef6fee 0xfffff3ff3fffffff 0xffffff3ff3ffffff

def z187 : W := mkw 0x0004020800208088 0x0000402080020808 0x80000208000080c8 0x080000208000080c

def z188 : W := mkw 0x0a00000240044155 0x00a0000024004415 0x8d88001fc30043fb 0x78d88001fc30043f

def z189 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0020018030003000 0x0002001803000300

def z190 : W := mkw 0x003d03dc00000000 0x7003d03dc0000000 0xbf3f83fe00000000 0x3bf3f83fe0000000

def z191 : W := mkw 0xe07ffffd95db0000 0x7e07ffffd95db000 0xff3fffffc0ff0004 0x3ff3fffffc0ff000

def z192 : W := mkw 0x0800000200044044 0x0080000020004404 0x8000000e000040c8 0x18000000e000040c

def z193 : W := mkw 0x003a480000000000 0x4003a48000000000 0x7f3ffc0000000000 0x07f3ffc000000000

def z194 : W := mkw 0x0805028e0024d0ce 0x10805028e0024d0c 0x8000038e0000f0c8 0x18000038e0000f0c

def z195 : W := mkw 0x803d23fd80000000 0x7803d23fd8000000 0x8f3803ffc0000000 0x38f3803ffc000000

def z196 : W := mkw 0x207a5c002f4b0000 0x4207a5c002f4b000 0x7f7ffc000f030002 0x07f7ffc000f03000

def z197 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffffffffcc008c0a 0xfffffffffcc008c0

def z198 : W := mkw 0xc83febff90b4d0ce 0x7c83febff90b4d0c 0xff3fffffc0fc00c4 0x3ff3fffffc0fc00c

def z199 : W := mkw 0xf07ffffdbfdb2a00 0x7f07ffffdbfdb2a0 0xffffffffffffff0f 0xfffffffffffffff0

def z200 : W := mkw 0x0800000200044044 0x0080000020004404 0xb500000e001c40cd 0x5b500000e001c40c

def z201 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xf727ff8fc0000000 0x1f727ff8fc000000

def z202 : W := mkw 0x207a5c002f4b0000 0x4207a5c002f4b000 0x4f787c003f030003 0xc4f787c003f03000

def z203 : W := mkw 0x0801008600045046 0x1080100860004504 0x0000018600007000 0x1000001860000700

def z204 : W := mkw 0x2000040001090000 0x0200004000109000 0xfd880c09031f00ff 0x6fd880c09031f00f

def z205 : W := mkw 0x4c05a2af10b4d4ee 0x14c05a2af10b4d4e 0xb7a783ef30fcfcfd 0xfb7a783ef30fcfcf

def z206 : W := mkw 0x04043229046284a8 0x004043229046284a 0x8bd472600ce08c0a 0xe8bd472600ce08c0

def z207 : W := mkw 0x2000040001090000 0x0200004000109000 0x70000c00001f0004 0x070000c00001f000

def z208 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xbff783ee3cfcfccf 0xfbff783ee3cfcfcc

def z209 : W := mkw 0x0038015000000000 0x6003801500000000 0xff380fffc0000000 0x3ff380fffc000000

def z210 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3ffffff000f009 0xfff3ffffff000f00

def z211 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x7d080c0fc31f00f7 0x47d080c0fc31f00f

def z212 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3007800e30fcf0cd 0xc3007800e30fcf0c

def z213 : W := mkw 0x4c00900214f6d4ee 0x04c00900214f6d4e 0x00c000003cfffcff 0xc00c000003cfffcf

def z214 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x7d880c00031f43ff 0x47d880c00031f43f

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000009000300f4 0x050000009000300f

def z216 : W := mkw 0x803b49d480000000 0x7803b49d48000000 0x0023818000000000 0x0002381800000000

def z217 : W := mkw 0x4c05b2af14f6d4ee 0x14c05b2af14f6d4e 0xfff7f3ef3cfffcff 0xffff7f3ef3cfffcf

def z218 : W := mkw 0x20425c00054b0000 0x020425c00054b000 0x40007c0000030000 0x040007c000003000

def z219 : W := mkw 0x0800000200044044 0x0080000020004404 0x00000000001c40cd 0x400000000001c40c

def z220 : W := mkw 0x1000015000002a00 0x21000015000002a0 0x8d8803f00300ff0b 0x78d8803f00300ff0

def z221 : W := mkw 0x04043229046284a8 0x004043229046284a 0xffdc7e7fcce38cfe 0xfffdc7e7fcce38cf

def z222 : W := mkw 0xc83febff90945046 0x7c83febff9094504 0xff3ffffff01c7001 0x3ff3ffffff01c700

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0x0888001003000302 0x2088800100300030

def z224 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x067803f03f00ff01 0x9067803f03f00ff0

def z225 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0x0277f3e03c00bc00 0x80277f3e03c00bc0

def z226 : W := mkw 0x2e04362b456fc5fd 0x02e04362b456fc5f 0xdbd472690fffcfff 0xedbd472690fffcff

def z227 : W := mkw 0x803f6aad80000000 0x5803f6aad8000000 0x7f3ffc0fc0000000 0x07f3ffc0fc000000

def z228 : W := mkw 0x0004222900000000 0x0000422290000000 0x5004700900000000 0x0500470090000000

def z229 : W := mkw 0x0c0532af0466d4ee 0x10c0532af0466d4e 0xdbd473ef0ce3fcfe 0xfdbd473ef0ce3fcf

def z230 : W := mkw 0x0a00000240044155 0x00a0000024004415 0xb580001fc01c43fd 0x7b580001fc01c43f

def z231 : W := mkw 0x4000800010900000 0x0400080001090000 0x3007800000fc0004 0x03007800000fc000

def z232 : W := mkw 0x6a7fde8e7fffd1df 0x56a7fde8e7fffd1d 0xffffff9ffffff3ff 0xfffffff9ffffff3f

def z233 : W := mkw 0x6042dc003fdb0000 0x06042dc003fdb000 0x7047fc003fff0007 0xc7047fc003fff000

def z234 : W := mkw 0x0400302104420420 0x0040030210442042 0x5bd470610ce30c36 0xe5bd470610ce30c3

def z235 : W := mkw 0x04043229046284a8 0x004043229046284a 0x80c002690ce38cfe 0xe80c002690ce38cf

def z236 : W := mkw 0x4801808610945046 0x1480180861094504 0x3727818630fc7005 0xd3727818630fc700

def z237 : W := mkw 0x1000015000002a00 0x21000015000002a0 0x0080007000000f00 0x20080007000000f0

def z238 : W := mkw 0x6a05868e51bdd1df 0x16a05868e51bdd1d 0xb7a7838e33fff3ff 0xdb7a7838e33fff3f

def z239 : W := mkw 0x647efe293ffb84a8 0x4647efe293ffb84a 0x7f7ffc093fff00f7 0xc7f7ffc093fff00f

def z240 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xff7ffffffc00bc00 0xbff7ffffffc00bc0

def z241 : W := mkw 0x787fdfde3fffface 0x7787fdfde3ffffac 0xfffffffe3fffffcf 0xffffffffe3fffffc

def z242 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xffa7838f30fff0ff 0xfffa7838f30fff0f

def z243 : W := mkw 0x0000000000000000 0x0000000000000000 0x08d000600c000c02 0x208d000600c000c0

def z244 : W := mkw 0x0c0522af0024d4ee 0x10c0522af0024d4e 0x808003ef0000fcf8 0x3808003ef0000fcf

def z245 : W := mkw 0x704094003fdb2a00 0x0704094003fdb2a0 0x00c000003fffff0f 0xc00c000003fffff0

def z246 : W := mkw 0x140432292e62aea8 0x0140432292e62aea 0xdbd472693fe3ffff 0xedbd472693fe3fff

def z247 : W := mkw 0x8a3f6bffc0044155 0x78a3f6bffc004415 0xffbfffffc00043f8 0x3ffbfffffc00043f

def z248 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x48880c11c31f43ff 0x648880c11c31f43f

def z249 : W := mkw 0xc03febfd90b0908a 0x7c03febfd90b0908 0x0237f3e030e0b000 0x80237f3e030e0b00

def z250 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffbfffffc300430b 0x7ffbfffffc300430

def z251 : W := mkw 0x583d83de3ab4face 0x7583d83de3ab4fac 0xbfff83fe3ffcffcf 0xfbfff83fe3ffcffc

def z252 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x0277f0003fff0007 0xc0277f0003fff000

def z253 : W := mkw 0x6a7adc027fdf4155 0x46a7adc027fdf415 0x7ffffc003fff43ff 0xc7ffffc003fff43f

def z254 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfd080c1fc31c4301 0x3fd080c1fc31c430

def z255 : W := mkw 0x183d03de2a24face 0x7183d03de2a24fac 0x8ff803fe3f00ffcb 0xf8ff803fe3f00ffc

def z256 : W := mkw 0xa07f7ffdaf4b0000 0x7a07f7ffdaf4b000 0xff7fffffcf030002 0x3ff7fffffcf03000

def z257 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xff3ffffff3007301 0x3ff3ffffff300730

def z258 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0af803f03f00bf02 0xa0af803f03f00bf0

def z259 : W := mkw 0x4c05b2af14f6d4ee 0x14c05b2af14f6d4e 0xf727f38f30fff0fd 0xdf727f38f30fff0f

def z260 : W := mkw 0x6042cc0011990000 0x06042cc001199000 0x20038c00001c0000 0x020038c00001c000

def z261 : W := mkw 0x607add503fdb0000 0x6607add503fdb000 0xff7ffff03fff0007 0xfff7ffff03fff000

def z262 : W := mkw 0x003800002a000000 0x4003800002a00000 0x8f7803803f00f00b 0xd8f7803803f00f00

def z263 : W := mkw 0x040532ad046284a8 0x1040532ad046284a 0xfff7f3ef0ce38cfe 0xffff7f3ef0ce38cf

def z264 : W := mkw 0x0200000040000111 0x0020000004000011 0x00800011c0000330 0x200800011c000033

def z265 : W := mkw 0xc03febfd90b0908a 0x7c03febfd90b0908 0xff3ffffff0e0b000 0xbff3ffffff0e0b00

def z266 : W := mkw 0x0400302104420420 0x0040030210442042 0x4000700100030030 0x0400070010003003

def z267 : W := mkw 0x800522ad80000000 0x1800522ad8000000 0x0000000fc0000000 0x00000000fc000000

def z268 : W := mkw 0x1000000000002a00 0x01000000000002a0 0x008000000000ff08 0x0008000000000ff0

def z269 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0x8ffff3f03f00ff0b 0xf8ffff3f03f00ff0

def z270 : W := mkw 0x0000100004420000 0x0000010000442000 0x025470000ce00000 0x8025470000ce0000

def z271 : W := mkw 0xaa3b4dd6c10d4155 0x7aa3b4dd6c10d415 0xfdab8d9fc31f43ff 0x7fdab8d9fc31f43f

def z272 : W := mkw 0x0000100004420000 0x0000010000442000 0x5004700000e30004 0x05004700000e3000

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0x00800000000300fe 0x400800000000300f

def z274 : W := mkw 0x043c3379046284a8 0x6043c3379046284a 0xdffc73f90ce38cfe 0xfdffc73f90ce38cf

def z275 : W := mkw 0x483d83de10b4d0ce 0x7483d83de10b4d0c 0xbf3f83fe30fcf0cd 0xfbf3f83fe30fcf0c

def z276 : W := mkw 0x0004222900000000 0x0000422290000000 0x8000026900000000 0x2800002690000000

def z277 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0008001003000300 0x0000800100300030

def z278 : W := mkw 0x04001000046284a8 0x004001000046284a 0x004000000ce08c00 0x8004000000ce08c0

def z279 : W := mkw 0x687fde8e3fffd0ce 0x5687fde8e3fffd0c 0xff7fff8e3ffff0cf 0xdff7fff8e3ffff0c

def z280 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb007838e00fcf0cc 0x1b007838e00fcf0c

def z281 : W := mkw 0xc807eaaf90b4d0ce 0x1c807eaaf90b4d0c 0xf727ff8ff0fcf0cd 0xdf727ff8ff0fcf0c

def z282 : W := mkw 0x0805028e0024d0ce 0x10805028e0024d0c 0xb727838e0000f0c8 0x1b727838e0000f0c

def z283 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x267ffc003ffc0001 0x8267ffc003ffc000

def z284 : W := mkw 0x227a5c006f4b0111 0x4227a5c006f4b011 0x48d87c11cf030332 0x248d87c11cf03033

def z285 : W := mkw 0x2e04362b456fc5fd 0x02e04362b456fc5f 0xfd8c7c1fc3ff43ff 0x7fd8c7c1fc3ff43f

def z286 : W := mkw 0x0000000000000000 0x0000000000000000 0x8d08001000000000 0x38d0800100000000

def z287 : W := mkw 0x0005028c00000000 0x10005028c0000000 0xb727838e3000f009 0xdb727838e3000f00

def z288 : W := mkw 0x247e7e292f6b84a8 0x4247e7e292f6b84a 0xdbdc7e690fe38cfe 0xedbdc7e690fe38cf

def z289 : W := mkw 0xe07bcdd4bb990000 0x7e07bcdd4bb99000 0x242b8d96f31c0001 0x1242b8d96f31c000

def z290 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x785ffc000fff0006 0x0785ffc000fff000

def z291 : W := mkw 0x04042229002084a8 0x004042229002084a 0x00000009000000f0 0x000000009000000f

def z292 : W := mkw 0x04001000046284a8 0x004001000046284a 0x8bd002600ce38cfe 0xe8bd002600ce38cf

def z293 : W := mkw 0x3a3805526b0d6b55 0x63a3805526b0d6b5 0xfdd80c7fcf1f4fff 0x7fdd80c7fcf1f4ff

def z294 : W := mkw 0x6a4094027fdf4155 0x06a4094027fdf415 0xfdc80c1fffff43ff 0xffdc80c1fffff43f

def z295 : W := mkw 0x3a3805526b0d6b55 0x63a3805526b0d6b5 0xaff80ff6ff1cff0b 0xfaff80ff6ff1cff0

def z296 : W := mkw 0x0800000200044044 0x0080000020004404 0x24000006001c4001 0x124000006001c400

def z297 : W := mkw 0x2e001402456fc5fd 0x02e001402456fc5f 0xfdc80c1fcfffcfff 0xffdc80c1fcfffcff

def z298 : W := mkw 0x687fde8e3fffd0ce 0x5687fde8e3fffd0c 0x7f7ffc0e3fff00c7 0xc7f7ffc0e3fff00c

def z299 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x74080c1fc31f43f5 0x174080c1fc31f43f

def z300 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xdff803f93f03ffff 0xfdff803f93f03fff

def z301 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xa4880c1fc31c43f9 0x3a4880c1fc31c43f

def z302 : W := mkw 0x1a00015240046b55 0x21a00015240046b5 0x808003ffc000fff8 0x3808003ffc000fff

def z303 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xfff80fffff00ff0b 0xffff80fffff00ff0

def z304 : W := mkw 0x1038015000002a00 0x61038015000002a0 0x8fb803f00000ff08 0x38fb803f00000ff0

def z305 : W := mkw 0x003800002a000000 0x4003800002a00000 0x0f7800003f000003 0xc0f7800003f00000

def z306 : W := mkw 0x26043629456b85b9 0x026043629456b85b 0xdbdc7e79cfe38ffe 0xedbdc7e79cfe38ff

def z307 : W := mkw 0x604084003b990000 0x0604084003b99000 0x00000000331c0001 0x000000000331c000

def z308 : W := mkw 0x800523fd80000000 0x3800523fd8000000 0xdb1473ffc0000000 0x3db1473ffc000000

def z309 : W := mkw 0x04043229046284a8 0x004043229046284a 0xc8d072690c038cfa 0x2c8d072690c038cf

def z310 : W := mkw 0x3a3805526b0d6b55 0x63a3805526b0d6b5 0xfda80d9ff31f73ff 0x7fda80d9ff31f73f

def z311 : W := mkw 0x4000900014d20000 0x04000900014d2000 0x7f77f0003cff0007 0xc7f77f0003cff000

def z312 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xc8187fffc0000000 0x3c8187fffc000000

def z313 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x8080001fc31f43ff 0x78080001fc31f43f

def z314 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xfffffe603fff8c0f 0xefffffe603fff8c0

def z315 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7277fc003cff0004 0x87277fc003cff000

def z316 : W := mkw 0x6a7acc027b9d4155 0x46a7acc027b9d415 0x242b8c16f31c4301 0x1242b8c16f31c430

def z317 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x08d800703f00ff0b 0xe08d800703f00ff0

def z318 : W := mkw 0x5805828e3ab4face 0x15805828e3ab4fac 0xb7e7838e3ffcffcf 0xdb7e7838e3ffcffc

def z319 : W := mkw 0x0c04322b0466c4ec 0x00c04322b0466c4e 0xffd4726f0cffccff 0xfffd4726f0cffccf

def z320 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x877003e03c00fc09 0xd877003e03c00fc0

def z321 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xff7ffc1fffff0007 0xfff7ffc1fffff000

def z322 : W := mkw 0x103800002a002a00 0x4103800002a002a0 0x0ff800003f00ff0b 0xc0ff800003f00ff0

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0x1304000000e00004 0xc1304000000e0000

def z324 : W := mkw 0x4804820a10b4d0ce 0x04804820a10b4d0c 0x9304020830fcf0cd 0xc9304020830fcf0c

def z325 : W := mkw 0x003a48002a000000 0x4003a48002a00000 0x7f7ffc003f000003 0xc7f7ffc003f00000

def z326 : W := mkw 0x140010002e62aea8 0x0140010002e62aea 0x00c000003fe3ffff 0xc00c000003fe3fff

def z327 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x7237ffefc0000000 0x07237ffefc000000

def z328 : W := mkw 0x4801808610945046 0x1480180861094504 0xb523818e301c70cd 0x5b523818e301c70c

def z329 : W := mkw 0x0a05028e4024d1df 0x10a05028e4024d1d 0x8080039fc000f3f8 0x38080039fc000f3f

def z330 : W := mkw 0x507ad9503ed22a00 0x6507ad9503ed22a0 0x8ffff3f03fe0ff0b 0xf8ffff3f03fe0ff0

def z331 : W := mkw 0x0000000000000000 0x0000000000000000 0x48080c11c0000000 0x248080c11c000000

def z332 : W := mkw 0x803f7bfd84420000 0x7803f7bfd8442000 0xff7fffffcce30006 0xfff7fffffcce3000

def z333 : W := mkw 0x1000015000002a00 0x21000015000002a0 0x0000019000007300 0x1000001900000730

def z334 : W := mkw 0x4c05b2af14f6d4ee 0x14c05b2af14f6d4e 0x7007f00f00ff00f4 0x07007f00f00ff00f

def z335 : W := mkw 0x04043229046284a8 0x004043229046284a 0xd084726900e38cfc 0x2d084726900e38cf

def z336 : W := mkw 0x6847de8e15ffd0ce 0x16847de8e15ffd0c 0xf727ff8e30fff0cd 0xdf727ff8e30fff0c

def z337 : W := mkw 0x4800800210b4d0ce 0x04800800210b4d0c 0xb500000e30fcf0cd 0xdb500000e30fcf0c

def z338 : W := mkw 0x0000000000000000 0x0000000000000000 0x8b10026000000000 0x28b1002600000000

def z339 : W := mkw 0x6000840011990000 0x0600084001199000 0x7f2f8c0033ff0007 0xc7f2f8c0033ff000

def z340 : W := mkw 0x2200040041090111 0x0220004004109011 0x40000c01c0030030 0x040000c01c003003

def z341 : W := mkw 0x003800002a000000 0x4003800002a00000 0x085800000f000002 0x0085800000f00000

def z342 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3727800e30fc00c5 0xc3727800e30fc00c

def z343 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7b57fc000cff0006 0xc7b57fc000cff000

def z344 : W := mkw 0x2200040041090111 0x0220004004109011 0x00080c10c3000300 0x000080c10c300030

def z345 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0x0007800000e00000 0x00007800000e0000

def z346 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7f7fffe03fffbc07 0xc7f7fffe03fffbc0

def z347 : W := mkw 0x4042d80014d20000 0x04042d80014d2000 0x0007f00000e00000 0x00007f00000e0000

def z348 : W := mkw 0x707adc003fdb2a00 0x4707adc003fdb2a0 0x7ffffc003fffff0f 0xc7ffffc003fffff0

def z349 : W := mkw 0x0000100004420000 0x0000010000442000 0x004000000ce30006 0xc004000000ce3000

def z350 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd880c1fc300430b 0x7fd880c1fc300430

def z351 : W := mkw 0x0004222900000000 0x0000422290000000 0xdb947269000300fe 0x6db947269000300f

def z352 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xffd80e7fcf1fcfff 0xfffd80e7fcf1fcff

def z353 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8bf003e03c00bc0a 0xe8bf003e03c00bc0

def z354 : W := mkw 0x407ad8003ed20000 0x4407ad8003ed2000 0x5b77f0003ce30006 0xc5b77f0003ce3000

def z355 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfd080c1fc01f00f4 0x3fd080c1fc01f00f

def z356 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x0227838030fcf0cd 0xc0227838030fcf0c

def z357 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdb5472690ce08c00 0xadb5472690ce08c0

def z358 : W := mkw 0x6e7efe2b7fffc5fd 0x46e7efe2b7fffc5f 0xfffffe7fffffcfff 0xffffffe7fffffcff

def z359 : W := mkw 0x803a495080000000 0x6803a49508000000 0x00080c10c0000000 0x000080c10c000000

def z360 : W := mkw 0xd83febffbab4face 0x7d83febffbab4fac 0xfffffffffffcffcf 0xffffffffffffcffc

def z361 : W := mkw 0x0000000000000000 0x0000000000000000 0xb500000e00000000 0x1b500000e0000000

def z362 : W := mkw 0x04042229002084a8 0x004042229002084a 0xd980026900038cfe 0x6d980026900038cf

def z363 : W := mkw 0x080000020024d0ce 0x0080000020024d0c 0x000000000000f0c8 0x0000000000000f0c

def z364 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0cf801f03f007f03 0x30cf801f03f007f0

def z365 : W := mkw 0x0004020800208088 0x0000402080020808 0x9bd402680ce08cce 0xe9bd402680ce08cc

def z366 : W := mkw 0x6805868e11bdd0ce 0x16805868e11bdd0c 0xff2f8f8e33fff0cf 0xdff2f8f8e33fff0c

def z367 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xdb37f3e900000000 0x2db37f3e90000000

def z368 : W := mkw 0x0805028e0024d0ce 0x10805028e0024d0c 0x9304038e00e0f0cc 0xd9304038e00e0f0c

def z369 : W := mkw 0x604094003fdb0000 0x0604094003fdb000 0x7d480c003fff0007 0xc7d480c003fff000

def z370 : W := mkw 0x2e001402456fc5fd 0x02e001402456fc5f 0x00c000000fffcfff 0xc00c000000fffcff

def z371 : W := mkw 0x04043229046284a8 0x004043229046284a 0x58d470690ce30cf6 0x258d470690ce30cf

def z372 : W := mkw 0x2a3804026b0d4155 0x42a3804026b0d415 0xfff80c1fff1f43ff 0xffff80c1fff1f43f

def z373 : W := mkw 0xae3f7fffc56fc5fd 0x7ae3f7fffc56fc5f 0xffffffffcfffcfff 0xfffffffffcfffcff

def z374 : W := mkw 0x4800800210b4d0ce 0x04800800210b4d0c 0x0000000000fc00c4 0x00000000000fc00c

def z375 : W := mkw 0x4004820810b08088 0x04004820810b0808 0xb727820830fc80cd 0xcb727820830fc80c

def z376 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x78880c1fc31f03f6 0x278880c1fc31f03f

def z377 : W := mkw 0x6a018486519d5157 0x16a018486519d515 0x242b8d96f31c7301 0x1242b8d96f31c730

def z378 : W := mkw 0x2200040041090111 0x0220004004109011 0x7d880c11c31f0337 0x67d880c11c31f033

def z379 : W := mkw 0x6845968e3fffd0ce 0x16845968e3fffd0c 0xb767838e3ffff0cf 0xdb767838e3ffff0c

def z380 : W := mkw 0x6a05868e51bdd1df 0x16a05868e51bdd1d 0xfd8f8c1fc3ff43ff 0x7fd8f8c1fc3ff43f

def z381 : W := mkw 0xa07a7d71af4b0000 0x6a07a7d71af4b000 0x48587c71cf030002 0x248587c71cf03000

def z382 : W := mkw 0x943f7bfdae62aea8 0x7943f7bfdae62aea 0xffffffffffe3ffff 0xfffffffffffe3fff

def z383 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0x8727838030e0f009 0xd8727838030e0f00

def z384 : W := mkw 0xe87fffffbfffd0ce 0x7e87fffffbfffd0c 0xff7ffffffffff0cf 0xfff7ffffffffff0c

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0xdd880019030343ff 0x7dd880019030343f

def z386 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0f7801903f007303 0xd0f7801903f00730

def z387 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7ffffc703fff0f07 0xe7ffffc703fff0f0

def z388 : W := mkw 0x4c05b2af14f6d4ee 0x14c05b2af14f6d4e 0xb777f3ee3cfcfccd 0xdb777f3ee3cfcfcc

def z389 : W := mkw 0x143c23792a20aea8 0x6143c23792a20aea 0x8ff803f93f00fffb 0xf8ff803f93f00fff

def z390 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xfffffc103fff430f 0xffffffc103fff430

def z391 : W := mkw 0x0805028e0024d0ce 0x10805028e0024d0c 0x0000000e000000c0 0x00000000e000000c

def z392 : W := mkw 0x0000015000000000 0x2000001500000000 0x800003f000000000 0x3800003f00000000

def z393 : W := mkw 0x2a001402454f4155 0x02a001402454f415 0xffdc7c1fcfff43ff 0xfffdc7c1fcfff43f

def z394 : W := mkw 0x04043229046284a8 0x004043229046284a 0x525472690ce38cf4 0x8525472690ce38cf

def z395 : W := mkw 0x6040940015db0000 0x06040940015db000 0x0000000000ff0004 0x00000000000ff000

def z396 : W := mkw 0x003a480000000000 0x4003a48000000000 0xff3ffc1fc0000000 0x3ff3ffc1fc000000

def z397 : W := mkw 0x04003021046284a8 0x004003021046284a 0x48d070610ce38cfe 0xe48d070610ce38cf

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0x5b14700000000000 0x05b1470000000000

def z399 : W := mkw 0x003810002e420000 0x4003810002e42000 0x5f7c70003fe30007 0xc5f7c70003fe3000

def z400 : W := mkw 0x607fde8c3fdb0000 0x5607fde8c3fdb000 0xff7fff8e3fff0007 0xdff7fff8e3fff000

def z401 : W := mkw 0x803f4bdc80000000 0x7803f4bdc8000000 0xb72f8f9ec0000000 0x1b72f8f9ec000000

def z402 : W := mkw 0x4800800210945046 0x0480080021094504 0x00000000301c7001 0x000000000301c700

def z403 : W := mkw 0x0000000000000000 0x0000000000000000 0x91000008000000cc 0x491000008000000c

def z404 : W := mkw 0x6a7adc027fdf4155 0x46a7adc027fdf415 0x7f7ffc16ffff4307 0xd7f7ffc16ffff430

def z405 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xbfaf839e33fcf3cf 0xfbfaf839e33fcf3c

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x0d08000003000003 0x40d0800000300000

def z407 : W := mkw 0x404090003ed20000 0x0404090003ed2000 0x004000003ce00000 0x8004000003ce0000

def z408 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x742ffc0033ff0005 0x0742ffc0033ff000

def z409 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb727838e00fc00c4 0x1b727838e00fc00c

def z410 : W := mkw 0x6e05b6af55ffd5ff 0x16e05b6af55ffd5f 0xffffffffffffffff 0xffffffffffffffff

def z411 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x2627838630fcf001 0x92627838630fcf00

def z412 : W := mkw 0x707acd503b992a00 0x6707acd503b992a0 0xaffb8ff03f1cff0b 0xfaffb8ff03f1cff0

def z413 : W := mkw 0x0005028c00000000 0x10005028c0000000 0xff2f8f9fc0000000 0x3ff2f8f9fc000000

def z414 : W := mkw 0x307a5d502f4b2a00 0x6307a5d502f4b2a0 0xcff87ff03f03ff0b 0xfcff87ff03f03ff0

def z415 : W := mkw 0x447efa293ef284a8 0x4447efa293ef284a 0x0277f2603ce08c00 0x80277f2603ce08c0

def z416 : W := mkw 0x900523fd80002a00 0x3900523fd80002a0 0x808003ffc000ff08 0x3808003ffc000ff0

def z417 : W := mkw 0x103d03dc2a002a00 0x7103d03dc2a002a0 0xbfff83fe3f00ff0b 0xfbfff83fe3f00ff0

def z418 : W := mkw 0x143c33792e62aea8 0x6143c33792e62aea 0x027473e03ce0bc00 0x8027473e03ce0bc0

def z419 : W := mkw 0x843f7bfd846284a8 0x7843f7bfd846284a 0x0277f3e00ce08c00 0x80277f3e00ce08c0

def z420 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8bd802700f008f0a 0xe8bd802700f008f0

def z421 : W := mkw 0xc83bc9d690945046 0x7c83bc9d69094504 0x242b8d96f01c7001 0x1242b8d96f01c700

def z422 : W := mkw 0x803b49d480000000 0x7803b49d48000000 0xaf3b8ff6c0000000 0x3af3b8ff6c000000

def z423 : W := mkw 0x503d83dc3ab0ba8a 0x7503d83dc3ab0ba8 0x8fff83f03fe0ff0b 0xf8fff83f03fe0ff0

def z424 : W := mkw 0x1000015000002a00 0x21000015000002a0 0x87a003f03000ff09 0xf87a003f03000ff0

def z425 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xad880c16c31c430b 0x7ad880c16c31c430

def z426 : W := mkw 0x0038015000000000 0x6003801500000000 0x0428019000000000 0x1042801900000000

def z427 : W := mkw 0x4800800210b4d0ce 0x04800800210b4d0c 0x3727800030fcf0cd 0xc3727800030fcf0c

def z428 : W := mkw 0x843f7bfd846284a8 0x7843f7bfd846284a 0xff7fffffcce08c00 0xbff7fffffcce08c0

def z429 : W := mkw 0x100000002a002a00 0x0100000002a002a0 0x00c000000f000f02 0x000c000000f000f0

def z430 : W := mkw 0x003800002a000000 0x4003800002a00000 0x8ff802603f008c0b 0xe8ff802603f008c0

def z431 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c000000c008c0a 0xc00c000000c008c0

def z432 : W := mkw 0x143831712e422e20 0x6143831712e422e2 0x48d870710f030f32 0x248d870710f030f3

def z433 : W := mkw 0x4405b2ad14f294aa 0x14405b2ad14f294a 0x0277f3e03ce0bc00 0x80277f3e03ce0bc0

def z434 : W := mkw 0x2e003423454f4575 0x02e003423454f457 0xfdd87c7fcf1f4fff 0x7fdd87c7fcf1f4ff

def z435 : W := mkw 0x4000800010900000 0x0400080001090000 0x24238000301c0001 0x024238000301c000

def z436 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x8f3ff3f000000000 0x38f3ff3f00000000

def z437 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xc8880c1fc30343fa 0x3c8880c1fc30343f

def z438 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x84a803f03300ff09 0x384a803f03300ff0

def z439 : W := mkw 0x0400302104420420 0x0040030210442042 0xcbd072610c038c3a 0xecbd072610c038c3

def z440 : W := mkw 0x0000000000000000 0x0000000000000000 0x35000000001c0005 0x435000000001c000

def z441 : W := mkw 0x4c05b2af14f6d4ee 0x14c05b2af14f6d4e 0xfbd7f26f0cff8cfe 0xefbd7f26f0cff8cf

def z442 : W := mkw 0xaa076eafc10d4155 0x1aa076eafc10d415 0x7007fc0fc01f00f4 0x07007fc0fc01f00f

def z443 : W := mkw 0x403880003a900000 0x4403880003a90000 0x3f7f80003ffc0007 0xc3f7f80003ffc000

def z444 : W := mkw 0x4000800010900000 0x0400080001090000 0x0227800030e00000 0x80227800030e0000

def z445 : W := mkw 0x0000000000000000 0x0000000000000000 0x5900000000030006 0x4590000000003000

def z446 : W := mkw 0x28000402010d4044 0x028000402010d404 0xfd080c0e031f40cf 0x5fd080c0e031f40c

def z447 : W := mkw 0x903a6971aa002a00 0x6903a6971aa002a0 0xcff87ff1ff00ff0b 0xfcff87ff1ff00ff0

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x008000000300430b 0x4008000000300430

def z449 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xb580000e031f43ff 0x5b580000e031f43f

def z450 : W := mkw 0x0a00000240044155 0x00a0000024004415 0x0000000fc00000f0 0x00000000fc00000f

def z451 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x70800c0fc31f43ff 0x470800c0fc31f43f

def z452 : W := mkw 0xe07ffffdbfdb0000 0x7e07ffffdbfdb000 0x7f7fffe03fff0007 0xc7f7fffe03fff000

def z453 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8ff803f00f000f02 0x38ff803f00f000f0

def z454 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x872803903300f309 0xd872803903300f30

def z455 : W := mkw 0x607acc003b990000 0x4607acc003b99000 0x372f8c0033fc0005 0xc372f8c0033fc000

def z456 : W := mkw 0x0e04222b4024c5fd 0x00e04222b4024c5f 0x8080027fc000cff8 0x38080027fc000cff

def z457 : W := mkw 0x2a04262b410d4155 0x02a04262b410d415 0xff9c7e7fc31f43ff 0x7ff9c7e7fc31f43f

def z458 : W := mkw 0x1000015000002a00 0x21000015000002a0 0x8bd003f00c00ff0a 0xf8bd003f00c00ff0

def z459 : W := mkw 0x0a00000240044155 0x00a0000024004415 0xd980001fc00343fe 0x7d980001fc00343f

def z460 : W := mkw 0x143811502e62aea8 0x6143811502e62aea 0x8ff803f03fe3ffff 0xf8ff803f03fe3fff

def z461 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x00000000031c4301 0x000000000031c430

def z462 : W := mkw 0x207a5c002f4b0000 0x4207a5c002f4b000 0x5b5c7c000fe30006 0xc5b5c7c000fe3000

def z463 : W := mkw 0x323805506b092b11 0x6323805506b092b1 0x48d80c71cf030f32 0x248d80c71cf030f3

def z464 : W := mkw 0x580080023ab4face 0x0580080023ab4fac 0x00c000003ffcffcf 0xc00c000003ffcffc

def z465 : W := mkw 0x0000000000208088 0x0000000000020808 0x0000000000e080cc 0xc0000000000e080c

def z466 : W := mkw 0x2e04362b456fc5fd 0x02e04362b456fc5f 0x70047c0fc0ff00f4 0x070047c0fc0ff00f

def z467 : W := mkw 0x803e6b7980000000 0x6803e6b798000000 0xdb1c7e79c0000000 0x2db1c7e79c000000

def z468 : W := mkw 0x903f6bfd80002a00 0x7903f6bfd80002a0 0xffbfffffc000ff08 0x3ffbfffffc000ff0

def z469 : W := mkw 0x207a5c002f4b0000 0x4207a5c002f4b000 0x7d587c000f1f0007 0x47d587c000f1f000

def z470 : W := mkw 0x6a42dc0255df4155 0x06a42dc0255df415 0x7007fc0fc0ff00f4 0x07007fc0fc0ff00f

def z471 : W := mkw 0x8003488480000000 0x1800348848000000 0x20038c06c0000000 0x020038c06c000000

def z472 : W := mkw 0xe47ffffdbffb84a8 0x7e47ffffdbffb84a 0xffffffffffff8cff 0xfffffffffffff8cf

def z473 : W := mkw 0xaa076eafc10d4155 0x1aa076eafc10d415 0xfd8ffc1fc31f43ff 0x7fd8ffc1fc31f43f

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x800003800000f008 0x1800003800000f00

def z475 : W := mkw 0x407ad8003ed20000 0x4407ad8003ed2000 0x7f7ffc003ce00000 0x87f7ffc003ce0000

def z476 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x88d803f00f00ff0a 0x388d803f00f00ff0

def z477 : W := mkw 0x903d23fdaa002a00 0x7903d23fdaa002a0 0x8ff803ffff00ff0b 0xf8ff803ffff00ff0

def z478 : W := mkw 0x003c237900000000 0x6003c23790000000 0xdf3c73f900000000 0x3df3c73f90000000

def z479 : W := mkw 0x6a05868e51bdd1df 0x16a05868e51bdd1d 0x70078c0fc0ff00f4 0x070078c0fc0ff00f

def z480 : W := mkw 0xea7fffffffdf4155 0x7ea7fffffffdf415 0xffffffffffff43ff 0xfffffffffffff43f

def z481 : W := mkw 0x000000002a000000 0x0000000002a00000 0x004000003f000003 0xc004000003f00000

def z482 : W := mkw 0x0400302104420420 0x0040030210442042 0xd9d070690c030cfe 0x6d9d070690c030cf

def z483 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x8227838e30e0f0c8 0x98227838e30e0f0c

def z484 : W := mkw 0x0800000200044044 0x0080000020004404 0x3000000e001c00c4 0x03000000e001c00c

def z485 : W := mkw 0x2a05068e410d4155 0x12a05068e410d415 0xffaf8f9fc31f43ff 0x7ffaf8f9fc31f43f

def z486 : W := mkw 0x8000217180000000 0x2800021718000000 0x00000071c0000000 0x200000071c000000

def z487 : W := mkw 0x207a4c002b090000 0x4207a4c002b09000 0x00080c0003000000 0x000080c000300000

def z488 : W := mkw 0x323805506b092b11 0x6323805506b092b1 0xcff80ff1ff03ff3b 0xfcff80ff1ff03ff3

def z489 : W := mkw 0x2a04060a412dc1dd 0x02a04060a412dc1d 0xff8c0e1fc3ffc3ff 0xfff8c0e1fc3ffc3f

def z490 : W := mkw 0x843f7bfd84420420 0x7843f7bfd8442042 0xffffffffcc030c32 0x3ffffffffcc030c3

def z491 : W := mkw 0x687fce8e3bbdd0ce 0x5687fce8e3bbdd0c 0xb72f8f8e33fcf0cd 0xdb72f8f8e33fcf0c

def z492 : W := mkw 0xc83fcbde90b4d0ce 0x7c83fcbde90b4d0c 0xb72f8f9ef0fcf0cd 0xdb72f8f9ef0fcf0c

def z493 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8dd800700f004f0b 0x78dd800700f004f0

def z494 : W := mkw 0x0004120804628088 0x0000412080462808 0xdb5472080ce380ce 0xcdb5472080ce380c

def z495 : W := mkw 0x483d828e3ab4d0ce 0x5483d828e3ab4d0c 0xbf7f838e3ffcf0cf 0xdbf7f838e3ffcf0c

def z496 : W := mkw 0x0005028c00000000 0x10005028c0000000 0x8000038e00000000 0x18000038e0000000

def z497 : W := mkw 0x04041208046284a8 0x004041208046284a 0x93c402080ce38cfe 0xc93c402080ce38cf

def z498 : W := mkw 0x583d83de3ab4face 0x7583d83de3ab4fac 0xb72f839e33fcf3cd 0xdb72f839e33fcf3c

def z499 : W := mkw 0x647adc003ffb84a8 0x4647adc003ffb84a 0x7ffffc003fff8cff 0xc7ffffc003fff8cf

def z500 : W := mkw 0x0a00000240044155 0x00a0000024004415 0xfd880c1fc00043f8 0x3fd880c1fc00043f

def z501 : W := mkw 0x0000000000000000 0x0000000000000000 0x8500000000004009 0x5850000000000400

def z502 : W := mkw 0x4c04b22b14f6d4ee 0x04c04b22b14f6d4e 0xdbd472693cfffcff 0xedbd472693cfffcf

def z503 : W := mkw 0x0000000000000000 0x0000000000000000 0x8300020000008008 0xc830002000000800

def z504 : W := mkw 0x803a697180000000 0x6803a69718000000 0x7f3ffc71c0000000 0x27f3ffc71c000000

def z505 : W := mkw 0x143c33792e62aea8 0x6143c33792e62aea 0xdbf473e93ce3bcfe 0xedbf473e93ce3bcf

def z506 : W := mkw 0x4000800010900000 0x0400080001090000 0xb727838030fcf00d 0xdb727838030fcf00

def z507 : W := mkw 0x903a6971aa002a00 0x6903a6971aa002a0 0x48d87c71cf000f02 0x248d87c71cf000f0

def z508 : W := mkw 0x607ede083ffb8088 0x4607ede083ffb808 0xff7ffe083fff80cf 0xcff7ffe083fff80c

def z509 : W := mkw 0x843f7bfd846284a8 0x7843f7bfd846284a 0xdbf7f3e90ce38cfe 0xedbf7f3e90ce38cf

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd880c1fc00300fe 0x7fd880c1fc00300f

def z511 : W := mkw 0x103a49502a002a00 0x6103a49502a002a0 0xfffffff03f00ff0b 0xffffffff03f00ff0

def z512 : W := mkw 0x04043229046284a8 0x004043229046284a 0xd984700900e300fe 0x6d984700900e300f

def z513 : W := mkw 0x1000015000002a00 0x21000015000002a0 0x000003e00000bc00 0x0000003e00000bc0

def z514 : W := mkw 0x143831712e422e20 0x6143831712e422e2 0xcff873f13f03ff3b 0xfcff873f13f03ff3

def z515 : W := mkw 0x604094003fdb0000 0x0604094003fdb000 0x376780003fff0007 0xc376780003fff000

def z516 : W := mkw 0x0004222900000000 0x0000422290000000 0x0214726000000000 0x0021472600000000

def z517 : W := mkw 0x803b49d480000000 0x7803b49d48000000 0x7f3ffd96c0000000 0x17f3ffd96c000000

def z518 : W := mkw 0x04042229002084a8 0x004042229002084a 0x8bd002690c008cfa 0xe8bd002690c008cf

def z519 : W := mkw 0x0004222900208088 0x0000422290020808 0xdb14726900e080cc 0xedb14726900e080c

def z520 : W := mkw 0x003a480000000000 0x4003a48000000000 0x242b8c0000000000 0x0242b8c000000000

def z521 : W := mkw 0xaa3f6fffc10d4155 0x7aa3f6fffc10d415 0xff3fffffc01f00f4 0x3ff3fffffc01f00f

def z522 : W := mkw 0x2000040001090000 0x0200004000109000 0xfd880c10031f430f 0x7fd880c10031f430

def z523 : W := mkw 0x140423790020aea8 0x2140423790020aea 0x808003f90000fff8 0x3808003f90000fff

def z524 : W := mkw 0xa03f6ffd81090000 0x7a03f6ffd8109000 0xff3fffffc31f0007 0x7ff3fffffc31f000

def z525 : W := mkw 0x800523fd80000000 0x3800523fd8000000 0xb72783ffc0000000 0x3b72783ffc000000

def z526 : W := mkw 0x04042229002084a8 0x004042229002084a 0x0000026000008c00 0x00000026000008c0

def z527 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xa42b8fffc0000000 0x3a42b8fffc000000

def z528 : W := mkw 0x2200040041090111 0x0220004004109011 0xfd880c1fc3030332 0x3fd880c1fc303033

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x24080c16c0000000 0x124080c16c000000

def z530 : W := mkw 0x6a05868e51bdd1df 0x16a05868e51bdd1d 0xf7278f8ff0fff0fd 0xdf7278f8ff0fff0f

def z531 : W := mkw 0xc07ffbfdbed20000 0x7c07ffbfdbed2000 0x0277f3e03ce00000 0x80277f3e03ce0000

def z532 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x246b8c003fff0007 0xc246b8c003fff000

def z533 : W := mkw 0x0800000200044044 0x0080000020004404 0xfd080c1fc01c40cd 0x7fd080c1fc01c40c

def z534 : W := mkw 0x103c03582a20aa88 0x6103c03582a20aa8 0x9ffc03f83fe0ffcf 0xf9ffc03f83fe0ffc

def z535 : W := mkw 0x0005028c00208088 0x10005028c0020808 0xb727838e00e080cc 0xdb727838e00e080c

def z536 : W := mkw 0x604094003fdb0000 0x0604094003fdb000 0x5b5470003fff0007 0xc5b5470003fff000

def z537 : W := mkw 0x687adc023fdf4044 0x4687adc023fdf404 0xff7ffc0e3fff40cf 0xdff7ffc0e3fff40c

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x70000c0fc0000000 0x070000c0fc000000

def z539 : W := mkw 0xe07ffeadbfdb0000 0x5e07ffeadbfdb000 0x7f7ffc0fffff0007 0xc7f7ffc0fffff000

def z540 : W := mkw 0x840533fd846284a8 0x3840533fd846284a 0xdbd473ffcce38cfe 0xfdbd473ffcce38cf

def z541 : W := mkw 0x2e04262b412dc5fd 0x02e04262b412dc5f 0xfd880e7fc31fcfff 0x7fd880e7fc31fcff

def z542 : W := mkw 0x0038000000000000 0x4003800000000000 0x0f38000000000000 0x00f3800000000000

def z543 : W := mkw 0xc07ffbfdbed20000 0x7c07ffbfdbed2000 0xff7ffffffce00000 0xbff7ffffffce0000

def z544 : W := mkw 0x100000002a002a00 0x0100000002a002a0 0x8dc800103f00ff0b 0xf8dc800103f00ff0

def z545 : W := mkw 0x0000000000000000 0x0000000000000000 0x0408001003004301 0x1040800100300430

def z546 : W := mkw 0x0000000000000000 0x0000000000000000 0xdbd002690c038cfe 0xedbd002690c038cf

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000003000f009 0xc000000003000f00

def z548 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0f7803e03f00bc03 0xc0f7803e03f00bc0

def z549 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xd9800009031f43ff 0x6d9800009031f43f

def z550 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x48587c003fff0007 0xc48587c003fff000

def z551 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x0007f00000000000 0x00007f0000000000

def z552 : W := mkw 0x24043629056b84a8 0x024043629056b84a 0xffdc7e690fff8cff 0xeffdc7e690fff8cf

def z553 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8da801903300730b 0x78da801903300730

def z554 : W := mkw 0x7a7add527fdf6b55 0x67a7add527fdf6b5 0xffffffffffffffff 0xffffffffffffffff

def z555 : W := mkw 0x043c32292e6284a8 0x4043c32292e6284a 0xdffc72693fe38cff 0xedffc72693fe38cf

def z556 : W := mkw 0x407fda8c3ef2908a 0x5407fda8c3ef2908 0x0277f3803ce0b000 0x80277f3803ce0b00

def z557 : W := mkw 0x2a7a5c026f4f4155 0x42a7a5c026f4f415 0xfdd87c1fcf1f43ff 0x7fdd87c1fcf1f43f

def z558 : W := mkw 0x0004322904420000 0x0000432290442000 0xdb5472690ce30006 0xedb5472690ce3000

def z559 : W := mkw 0x0000100004420000 0x0000010000442000 0x485070000c030002 0x0485070000c03000

def z560 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xf0800c1fc01f43fc 0x3f0800c1fc01f43f

def z561 : W := mkw 0x0400100004420420 0x0040010000442042 0x00c000000c030c32 0x000c000000c030c3

def z562 : W := mkw 0x6446fe2915fb84a8 0x06446fe2915fb84a 0x7007fc0900ff00f4 0x07007fc0900ff00f

def z563 : W := mkw 0x2000040001090000 0x0200004000109000 0xfd080c1fc31f0007 0x7fd080c1fc31f000

def z564 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x7d080c16c31f4307 0x57d080c16c31f430

def z565 : W := mkw 0x0038015000000000 0x6003801500000000 0x8ff803f00c008c0a 0xf8ff803f00c008c0

def z566 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0x9327838830e0b0cc 0xc9327838830e0b0c

def z567 : W := mkw 0x3a000552410d6b55 0x23a000552410d6b5 0xfd880fffc31fffff 0x7fd880fffc31ffff

def z568 : W := mkw 0x483fca8e10b4d0ce 0x5483fca8e10b4d0c 0xff3fff8e30fcf0cd 0xdff3fff8e30fcf0c

def z569 : W := mkw 0x180503de0024face 0x3180503de0024fac 0x808003fe0000ffc8 0x3808003fe0000ffc

def z570 : W := mkw 0x4a05828e50b4d1df 0x14a05828e50b4d1d 0xb7a7839ff0fcf3fd 0xfb7a7839ff0fcf3f

def z571 : W := mkw 0x0804020a0024c0cc 0x00804020a0024c0c 0xb704020e00fcc0cd 0xdb704020e00fcc0c

def z572 : W := mkw 0x843a797184420420 0x6843a79718442042 0x48d87c71cc030c32 0x248d87c71cc030c3

def z573 : W := mkw 0x80076bfd80000000 0x380076bfd8000000 0xf007ffffc0000000 0x3f007ffffc000000

def z574 : W := mkw 0x0004020800208088 0x0000402080020808 0xdb84020900e380fe 0xedb84020900e380f

def z575 : W := mkw 0x0004020800208088 0x0000402080020808 0x9724038830e0f0cd 0xd9724038830e0f0c

def z576 : W := mkw 0xcc3ffbff94f6d4ee 0x7cc3ffbff94f6d4e 0xfffffffffcfffcff 0xffffffffffcfffcf

def z577 : W := mkw 0x0000202100000000 0x0000020210000000 0x4810706100000000 0x2481070610000000

def z578 : W := mkw 0x04043229046284a8 0x004043229046284a 0x935472680ce08ccc 0xc935472680ce08cc

def z579 : W := mkw 0x0005028c0020908a 0x10005028c0020908 0x000003800000b000 0x0000003800000b00

def z580 : W := mkw 0x247a7c212f4b0420 0x4247a7c212f4b042 0x48d87c610f030c32 0x248d87c610f030c3

def z581 : W := mkw 0x0805028e0024d0ce 0x10805028e0024d0c 0xb500038e001cf0cd 0x5b500038e001cf0c

def z582 : W := mkw 0x2200040041090111 0x0220004004109011 0xd9880c19c30303fe 0x6d9880c19c30303f

def z583 : W := mkw 0x103c23792a002a00 0x6103c23792a002a0 0xdffc73f93f00ff0b 0xfdffc73f93f00ff0

def z584 : W := mkw 0x687bcc863b9d5046 0x5687bcc863b9d504 0x242b8d86331c7001 0x1242b8d86331c700

def z585 : W := mkw 0x507ad9503ed22a00 0x6507ad9503ed22a0 0x0277f3e03ce0bc00 0x80277f3e03ce0bc0

def z586 : W := mkw 0xe07afd71bfdb0000 0x6e07afd71bfdb000 0x7f7ffc71ffff0007 0xe7f7ffc71ffff000

def z587 : W := mkw 0x0005028c00000000 0x10005028c0000000 0x3007800e00000000 0x03007800e0000000

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x80800009000000f8 0x280800009000000f

def z589 : W := mkw 0x26003421454b0531 0x026003421454b053 0x48d87c71cf030f32 0x248d87c71cf030f3

def z590 : W := mkw 0x0001008400000000 0x1000100840000000 0x2423818600000000 0x1242381860000000

def z591 : W := mkw 0x100000002a002a00 0x0100000002a002a0 0x0000000033007301 0x0000000003300730

def z592 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x24880c16c31f43ff 0x524880c16c31f43f

def z593 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x005000600c000c00 0x0005000600c000c0

def z594 : W := mkw 0x6a7adc027fdf4155 0x46a7adc027fdf415 0x7f7ffc0fffff00f7 0xc7f7ffc0fffff00f

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x8720038000000000 0x1872003800000000

def z596 : W := mkw 0x1a3801526a046b55 0x61a3801526a046b5 0x8ff803ffff00fffb 0xf8ff803ffff00fff

def z597 : W := mkw 0x883f6bff8024d0ce 0x7883f6bff8024d0c 0xff3fffffc000f0c8 0x3ff3fffffc000f0c

def z598 : W := mkw 0x2a3a4c02410d4155 0x42a3a4c02410d415 0xffbffc1fc31f43ff 0x7ffbffc1fc31f43f

def z599 : W := mkw 0x003a495000000000 0x6003a49500000000 0xff3ffff000000000 0x3ff3ffff00000000

def z600 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x4a3ffff1c0000000 0x24a3ffff1c000000

def z601 : W := mkw 0x0038015000000000 0x6003801500000000 0x023003e000000000 0x0023003e00000000

def z602 : W := mkw 0x04043229046284a8 0x004043229046284a 0x5b5470090ce300f6 0xc5b5470090ce300f

def z603 : W := mkw 0x407ac8003a900000 0x4407ac8003a90000 0x0023800030000000 0x0002380003000000

def z604 : W := mkw 0x0000000000000000 0x0000000000000000 0x8080026000008c08 0x28080026000008c0

def z605 : W := mkw 0xaa3f6fffc10d4155 0x7aa3f6fffc10d415 0xff3fffffc31c4301 0x3ff3fffffc31c430

def z606 : W := mkw 0x583981d63a947a46 0x7583981d63a947a4 0x242b8196331c7301 0x1242b8196331c730

def z607 : W := mkw 0x0a00000240044155 0x00a0000024004415 0x00000016c0004300 0x100000016c000430

def z608 : W := mkw 0x6c7ffeaf3fffd4ee 0x56c7ffeaf3fffd4e 0xffffffef3ffffcff 0xfffffffef3ffffcf

def z609 : W := mkw 0x3a3805526b0d6b55 0x63a3805526b0d6b5 0x24280d96f31c7301 0x124280d96f31c730

def z610 : W := mkw 0x803a697180000000 0x6803a69718000000 0xcf387ff1c0000000 0x3cf387ff1c000000

def z611 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x8237f3ffc0000000 0x38237f3ffc000000

def z612 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xa423838e301cf0c9 0x1a423838e301cf0c

def z613 : W := mkw 0xe047fead95db0000 0x1e047fead95db000 0x7007fc0fc0ff0004 0x07007fc0fc0ff000

def z614 : W := mkw 0x6a018486519d5157 0x16a018486519d515 0xfdab8d9ff31f73ff 0x7fdab8d9ff31f73f

def z615 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8f3803f033007301 0x38f3803f03300730

def z616 : W := mkw 0x003800002a000000 0x4003800002a00000 0x027000003c000000 0x8027000003c00000

def z617 : W := mkw 0x0805028e00044044 0x10805028e0004404 0xb727838e001c40cd 0x5b727838e001c40c

def z618 : W := mkw 0x583881523ab4face 0x6583881523ab4fac 0x8ff803f03ffcffcf 0xf8ff803f03ffcffc

def z619 : W := mkw 0x04043229046284a8 0x004043229046284a 0x5b5472600ce38c06 0xc5b5472600ce38c0

def z620 : W := mkw 0x644094003ffb84a8 0x0644094003ffb84a 0x00c000003fff8cff 0xc00c000003fff8cf

def z621 : W := mkw 0x607fde8c3ffb908a 0x5607fde8c3ffb908 0x7f7fff803fffb007 0xc7f7fff803fffb00

def z622 : W := mkw 0x0e04322b4466c5fd 0x00e04322b4466c5f 0xdbd4727fcce3cffe 0xfdbd4727fcce3cff

def z623 : W := mkw 0x043e7a29046284a8 0x4043e7a29046284a 0xfffffe690ce38cfe 0xefffffe690ce38cf

def z624 : W := mkw 0x4001808410901002 0x1400180841090100 0x0023818030003000 0x0002381803000300

def z625 : W := mkw 0x4805928e14f6d0ce 0x14805928e14f6d0c 0xff77f38e3cfff0cf 0xdff77f38e3cfff0c

def z626 : W := mkw 0x607adc0015db0000 0x4607adc0015db000 0x7f3ffc0000ff0004 0x07f3ffc0000ff000

def z627 : W := mkw 0x04043229046284a8 0x004043229046284a 0x82d472690ce08cf8 0xa82d472690ce08cf

def z628 : W := mkw 0x4000800010900000 0x0400080001090000 0x0000000030fc0005 0xc0000000030fc000

def z629 : W := mkw 0x0004020800208088 0x0000402080020808 0x1004000800e000c4 0x01004000800e000c

def z630 : W := mkw 0x4000800010b0908a 0x04000800010b0908 0x0000000030e0b000 0x80000000030e0b00

def z631 : W := mkw 0x803a697180000000 0x6803a69718000000 0xfd187c7fc0000000 0x3fd187c7fc000000

def z632 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x82f003f03c00ff08 0xb82f003f03c00ff0

def z633 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb307820e00fc80cc 0xcb307820e00fc80c

def z634 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x4a7ffc003fe30002 0x84a7ffc003fe3000

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x4880000100030032 0x2488000010003003

def z636 : W := mkw 0x140433790462aea8 0x2140433790462aea 0xdbd473f90ce3fffe 0xfdbd473f90ce3fff

def z637 : W := mkw 0x0000000000000000 0x0000000000000000 0x0420018030007001 0x1042001803000700

def z638 : W := mkw 0x0400302104420420 0x0040030210442042 0x005070600c000c00 0x0005070600c000c0

def z639 : W := mkw 0x100000002a002a00 0x0100000002a002a0 0x004000003c00bc00 0x8004000003c00bc0

def z640 : W := mkw 0x0000000000000000 0x0000000000000000 0x022003803000b000 0x8022003803000b00

def z641 : W := mkw 0x607acc003b990000 0x4607acc003b99000 0x7d2b8c00331f0007 0x47d2b8c00331f000

def z642 : W := mkw 0x000522ad00000000 0x1000522ad0000000 0xff37f3ef00000000 0x3ff37f3ef0000000

def z643 : W := mkw 0x183801522a046a44 0x6183801522a046a4 0xbff803fe3f1cffcf 0xfbff803fe3f1cffc

def z644 : W := mkw 0x843e7b79846284a8 0x6843e7b79846284a 0xdbdc7e79cce38cfe 0xedbdc7e79cce38cf

def z645 : W := mkw 0x707895503fdb2a00 0x6707895503fdb2a0 0x8ff803f03fffff0f 0xf8ff803f03fffff0

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000001fc0000000 0x38000001fc000000

def z647 : W := mkw 0x6a00840251bdd1df 0x06a00840251bdd1d 0x0080000033fff3ff 0xc0080000033fff3f

def z648 : W := mkw 0x203a4c0001090000 0x4203a4c000109000 0x7f3ffc00031f0007 0x47f3ffc00031f000

def z649 : W := mkw 0x687bdc863fdf5046 0x5687bdc863fdf504 0x7f7ffd863fff7007 0xd7f7ffd863fff700

def z650 : W := mkw 0x4404b22914f284a8 0x04404b22914f284a 0xfff7f2693cff8cff 0xefff7f2693cff8cf

def z651 : W := mkw 0x607efe293fdb0000 0x4607efe293fdb000 0xff7ffe693fff0007 0xeff7ffe693fff000

def z652 : W := mkw 0x2200040041090111 0x0220004004109011 0xcd880c11c303433b 0x7cd880c11c303433

def z653 : W := mkw 0x883f6bff80044044 0x7883f6bff8004404 0xff3fffffc01c40cd 0x7ff3fffffc01c40c

def z654 : W := mkw 0x103811502e422a00 0x6103811502e422a0 0xdffc73f03fe3ff0f 0xfdffc73f03fe3ff0

def z655 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xf5000c0fc01f40fd 0x5f5000c0fc01f40f

def z656 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xb5080c1ec31c43cd 0x5b5080c1ec31c43c

def z657 : W := mkw 0x04042229002084a8 0x004042229002084a 0x9384026900e08cfc 0xe9384026900e08cf

def z658 : W := mkw 0x04000000002084a8 0x004000000002084a 0x0080000000008cf8 0x00080000000008cf

def z659 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8f7803f03c00bc00 0xb8f7803f03c00bc0

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0x0720000030000001 0xc072000003000000

def z661 : W := mkw 0x503881503a902a00 0x6503881503a902a0 0xbfff83f03ffcff0f 0xfbfff83f03ffcff0

def z662 : W := mkw 0x0000100004420000 0x0000010000442000 0xdbd472600ce38c0e 0xedbd472600ce38c0

def z663 : W := mkw 0x04043229046284a8 0x004043229046284a 0x0004700000e00000 0x00004700000e0000

def z664 : W := mkw 0x0004020800000000 0x0000402080000000 0x9304020800000000 0x0930402080000000

def z665 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x8000038e30fcf0cd 0xd8000038e30fcf0c

def z666 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x20000c06c01c0000 0x020000c06c01c000

def z667 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x6c7bfc003f1f0003 0x06c7bfc003f1f000

def z668 : W := mkw 0x203804002b090000 0x4203804002b09000 0x7f780c003f1f0007 0xc7f780c003f1f000

def z669 : W := mkw 0x04043229046284a8 0x004043229046284a 0x4ad472610ce38c32 0xa4ad472610ce38c3

def z670 : W := mkw 0x2a05068e412dd1df 0x12a05068e412dd1d 0xfd880f9fc31ff3ff 0x7fd880f9fc31ff3f

def z671 : W := mkw 0x843f7bfd846284a8 0x7843f7bfd846284a 0xff3fffffc0e300f4 0x3ff3fffffc0e300f

def z672 : W := mkw 0x0038015000000000 0x6003801500000000 0x8f3803f03000f009 0xf8f3803f03000f00

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x8fd802700f00cf0b 0xf8fd802700f00cf0

def z674 : W := mkw 0x447efa293ef284a8 0x4447efa293ef284a 0xdbf7f2693ce38cfe 0xedbf7f2693ce38cf

def z675 : W := mkw 0x4805828e10945046 0x14805828e1094504 0xb727838e301c7001 0x1b727838e301c700

def z676 : W := mkw 0x4c05928e14f6d4ee 0x14c05928e14f6d4e 0xb7e7838e3cfffcff 0xdb7e7838e3cfffcf

def z677 : W := mkw 0x3e3c377b6f6feffd 0x63e3c377b6f6feff 0xfffc7fffffffffff 0xffffc7ffffffffff

def z678 : W := mkw 0x6a05868e51bdd1df 0x16a05868e51bdd1d 0xb72f8f9ef3fcf3cd 0xdb72f8f9ef3fcf3c

def z679 : W := mkw 0x2000040001090000 0x0200004000109000 0x48080c0003030002 0x048080c000303000

def z680 : W := mkw 0x003a480000000000 0x4003a48000000000 0x48187c0000000000 0x048187c000000000

def z681 : W := mkw 0x007a58002e420000 0x4007a58002e42000 0x005070000c000000 0x0005070000c00000

def z682 : W := mkw 0x2200040041090111 0x0220004004109011 0x0080000003030332 0x0008000000303033

def z683 : W := mkw 0x0000100004420000 0x0000010000442000 0xdbd470090ce300fe 0xedbd470090ce300f

def z684 : W := mkw 0x6a00840251bdd1df 0x06a00840251bdd1d 0xfd880c1ff3fff3ff 0xffd880c1ff3fff3f

def z685 : W := mkw 0x4801808610945046 0x1480180861094504 0x20038006001c0000 0x020038006001c000

def z686 : W := mkw 0x20001400054b0000 0x020001400054b000 0x7f5c7c000fff0007 0xc7f5c7c000fff000

def z687 : W := mkw 0x580583de10b4face 0x3580583de10b4fac 0xb7a783fe30fcffcd 0xfb7a783fe30fcffc

def z688 : W := mkw 0xaa3a6d73c10d4155 0x6aa3a6d73c10d415 0xfd987c7fc31f43ff 0x7fd987c7fc31f43f

def z689 : W := mkw 0x003800002a000000 0x4003800002a00000 0x0428000033000001 0x0042800003300000

def z690 : W := mkw 0x4405b2ad14f294aa 0x14405b2ad14f294a 0xdbf7f3e93ce3bcfe 0xedbf7f3e93ce3bcf

def z691 : W := mkw 0x04001000046284a8 0x004001000046284a 0xd9c000090ce38cfe 0xed9c000090ce38cf

def z692 : W := mkw 0x583981d63a947a46 0x7583981d63a947a4 0xaffb83f63f1cff0b 0xfaffb83f63f1cff0

def z693 : W := mkw 0xa23f6ffdc1090111 0x7a23f6ffdc109011 0xffbfffffc3030332 0x3ffbfffffc303033

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x025002600c008c00 0x8025002600c008c0

def z695 : W := mkw 0x903b49d4aa002a00 0x7903b49d4aa002a0 0xaffb8ff6ff00ff0b 0xfaffb8ff6ff00ff0

def z696 : W := mkw 0x003a480000000000 0x4003a48000000000 0x0237f00000000000 0x00237f0000000000

def z697 : W := mkw 0x100000002a002a00 0x0100000002a002a0 0x8bd002603f00ff0b 0xe8bd002603f00ff0

def z698 : W := mkw 0x7a3d87de7bbdfbdf 0x77a3d87de7bbdfbd 0xffff8fffffffffff 0xfffff8ffffffffff

def z699 : W := mkw 0x4800800210944044 0x0480080021094404 0xb727800e30fc40cd 0xdb727800e30fc40c

def z700 : W := mkw 0xe07feffdbb990000 0x7e07feffdbb99000 0xff3ffffff31c0001 0x3ff3ffffff31c000

def z701 : W := mkw 0x503d83dc3ab0ba8a 0x7503d83dc3ab0ba8 0x027783e03ce0bc00 0x8027783e03ce0bc0

def z702 : W := mkw 0xaa0527ffc10d4155 0x3aa0527ffc10d415 0xfd880fffc31f43ff 0x7fd880fffc31f43f

def z703 : W := mkw 0x003e6a2900000000 0x4003e6a290000000 0xff3ffe6900000000 0x2ff3ffe690000000

def z704 : W := mkw 0x647efe293ffb84a8 0x4647efe293ffb84a 0x7f7ffe603fff8c07 0xc7f7ffe603fff8c0

def z705 : W := mkw 0x803b49d480000000 0x7803b49d48000000 0xfd2b8d9fc0000000 0x3fd2b8d9fc000000

def z706 : W := mkw 0x04042229002084a8 0x004042229002084a 0xdb94726900008cf8 0x2db94726900008cf

def z707 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0x742ffd9ff3007301 0x1742ffd9ff300730

def z708 : W := mkw 0x04043229046284a8 0x004043229046284a 0xffdc7e690ce38cfe 0xeffdc7e690ce38cf

def z709 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdbdc7e79cce38cfe 0xedbdc7e79cce38cf

def z710 : W := mkw 0x6042dc003fdb0000 0x06042dc003fdb000 0x0047f0003fff0007 0xc0047f0003fff000

def z711 : W := mkw 0x04043229046284a8 0x004043229046284a 0x505470690ce30cf4 0x0505470690ce30cf

def z712 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7ffffc603fff0c07 0xe7ffffc603fff0c0

def z713 : W := mkw 0x803b49d480000000 0x7803b49d48000000 0xff3ffff6c0000000 0x3ff3ffff6c000000

def z714 : W := mkw 0x2e04362b456fc5fd 0x02e04362b456fc5f 0x265c7e76cffccf01 0x9265c7e76cffccf0

def z715 : W := mkw 0x1c3d23ff2a24feee 0x71c3d23ff2a24fee 0x8ff803ff3f00fffb 0xf8ff803ff3f00fff

def z716 : W := mkw 0x103a49502a002a00 0x6103a49502a002a0 0xffffffffff00ff0b 0xfffffffffff00ff0

def z717 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xbf3783ee30fcf0cd 0xfbf3783ee30fcf0c

def z718 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7ffffc003fff8c0f 0xc7ffffc003fff8c0

def z719 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x86f803f03f00ff09 0xb86f803f03f00ff0

def z720 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8ff803f03f03ffff 0xf8ff803f03f03fff

def z721 : W := mkw 0x607add503fdb0000 0x6607add503fdb000 0xff7fffffffff0007 0xfff7fffffffff000

def z722 : W := mkw 0x80076aad80208088 0x180076aad8020808 0xf307fe0fc0e080cc 0xcf307fe0fc0e080c

def z723 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3fffffc0030006 0x7ff3fffffc003000

def z724 : W := mkw 0x000522ad00000000 0x1000522ad0000000 0xff3fffffc0000000 0x3ff3fffffc000000

def z725 : W := mkw 0x6a4094027fdf4155 0x06a4094027fdf415 0x004000003fff00f7 0xc004000003fff00f

def z726 : W := mkw 0x707adc003fdb2a00 0x4707adc003fdb2a0 0x7ffffc003fff0f07 0xc7ffffc003fff0f0

def z727 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xfb1ffe7fc0000000 0x2fb1ffe7fc000000

def z728 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x780ffc0003ff0006 0x0780ffc0003ff000

def z729 : W := mkw 0x583d83de3ab4face 0x7583d83de3ab4fac 0x38df807e0ffc0fc6 0x238df807e0ffc0fc

def z730 : W := mkw 0x4805a2af10b4d0ce 0x14805a2af10b4d0c 0xb737f3ee30fcf0cd 0xdb737f3ee30fcf0c

def z731 : W := mkw 0x6042dc003fdb0000 0x06042dc003fdb000 0x7d4ffc003fff0007 0xc7d4ffc003fff000

def z732 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb7e7838e3cfcfccf 0xdb7e7838e3cfcfcc

def z733 : W := mkw 0x040532ad046284a8 0x1040532ad046284a 0xffffffffcce38cfe 0xfffffffffcce38cf

def z734 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xfffffc193fff43ff 0xffffffc193fff43f

def z735 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xca3fffffc0000000 0x3ca3fffffc000000

def z736 : W := mkw 0x803b69f580000000 0x7803b69f58000000 0x7f3ffdf7c0000000 0x37f3ffdf7c000000

def z737 : W := mkw 0x843b59d4846284a8 0x7843b59d4846284a 0x24eb8d96cce38cfe 0xd24eb8d96cce38cf

def z738 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb327838e30fcb0cc 0xcb327838e30fcb0c

def z739 : W := mkw 0x6205868c51b9919b 0x16205868c51b9919 0x4aaf8f91f3e3b332 0xa4aaf8f91f3e3b33

def z740 : W := mkw 0x407ad8003ed20000 0x4407ad8003ed2000 0x3277f0003cfc0004 0x83277f0003cfc000

def z741 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x74880c1fc31f43ff 0x574880c1fc31f43f

def z742 : W := mkw 0x6e00940255ffd5ff 0x06e00940255ffd5f 0x00c000003fffffff 0xc00c000003ffffff

def z743 : W := mkw 0x803b49d480000000 0x7803b49d48000000 0xff3ffd9fc0000000 0x3ff3ffd9fc000000

def z744 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x2427818630fc7001 0x12427818630fc700

def z745 : W := mkw 0x840532ad846284a8 0x1840532ad846284a 0xdbd4726fcce38cfe 0xedbd4726fcce38cf

def z746 : W := mkw 0x803f6bfdaa000000 0x7803f6bfdaa00000 0xff3ffffff3000001 0x3ff3ffffff300000

def z747 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7f2ffc0033ff0007 0xc7f2ffc0033ff000

def z748 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3ffffff0000001 0xfff3ffffff000000

def z749 : W := mkw 0x04003021046284a8 0x004003021046284a 0x5bd470610ce38cfe 0xe5bd470610ce38cf

def z750 : W := mkw 0x4c01b0a714d65466 0x14c01b0a714d6546 0x6cf3f1e73c1f7c33 0x36cf3f1e73c1f7c3

def z751 : W := mkw 0x04043229046284a8 0x004043229046284a 0xd8d472690ce38cfe 0x2d8d472690ce38cf

def z752 : W := mkw 0x903f6bfd80002a00 0x7903f6bfd80002a0 0xffbfffffc300ff0b 0x7ffbfffffc300ff0

def z753 : W := mkw 0x143c33792e62aea8 0x6143c33792e62aea 0x542c719933e373f5 0x1542c719933e373f

def z754 : W := mkw 0x80076bfd80000000 0x380076bfd8000000 0x7007fd9fc0000000 0x17007fd9fc000000

def z755 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0x3227838030fcb004 0x83227838030fcb00

def z756 : W := mkw 0x8a0523ffc024d1df 0x38a0523ffc024d1d 0x808003ffc000f3f8 0x3808003ffc000f3f

def z757 : W := mkw 0x903b69f5aa002a00 0x7903b69f5aa002a0 0x6cfbfdf7ff007f03 0x36cfbfdf7ff007f0

def z758 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xffa80c1ff31f43ff 0xfffa80c1ff31f43f

def z759 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xffffffffffffff0f 0xfffffffffffffff0

def z760 : W := mkw 0x4000900014d20000 0x04000900014d2000 0x7007f00000ff0004 0x07007f00000ff000

def z761 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x7d0ffc0fc0000000 0x07d0ffc0fc000000

def z762 : W := mkw 0x100001502a002a00 0x2100001502a002a0 0x87e003f03f00ff0b 0xf87e003f03f00ff0

def z763 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xa627838e30fcf0c9 0x9a627838e30fcf0c

def z764 : W := mkw 0xb07a7d71af4b2a00 0x6b07a7d71af4b2a0 0x48d87c71cf030f02 0x248d87c71cf030f0

def z765 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xf007fc1fc0000000 0x3f007fc1fc000000

def z766 : W := mkw 0x843f6bfd802084a8 0x7843f6bfd802084a 0xffbfffffc0038cfe 0x7ffbfffffc0038cf

def z767 : W := mkw 0xc83ae97390b4d0ce 0x6c83ae97390b4d0c 0x48187c71f0fcf0cd 0xe48187c71f0fcf0c

def z768 : W := mkw 0x04003021046284a8 0x004003021046284a 0x00d070600ce38cfe 0xc00d070600ce38cf

def z769 : W := mkw 0x8e0523ffc024c5fd 0x38e0523ffc024c5f 0x808003ffc000cff8 0x3808003ffc000cff

def z770 : W := mkw 0x647eee293bb984a8 0x4647eee293bb984a 0xa4ab8e69331c8cf9 0x2a4ab8e69331c8cf

def z771 : W := mkw 0x4805a2af10b4d0ce 0x14805a2af10b4d0c 0xb72783ef30fcf0cd 0xfb72783ef30fcf0c

def z772 : W := mkw 0x4a7ad8027ed64155 0x44a7ad8027ed6415 0x82f7f01ffce043f8 0xb82f7f01ffce043f

def z773 : W := mkw 0x0000000000000000 0x0000000000000000 0x8ff803f03f00ff0b 0xf8ff803f03f00ff0

def z774 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3ffffff000b000 0xbff3ffffff000b00

def z775 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x0227838030fcf001 0x80227838030fcf00

def z776 : W := mkw 0x04043229046284a8 0x004043229046284a 0x8bd472600ce38cfe 0xe8bd472600ce38cf

def z777 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xbfff83f03f00ff0b 0xfbfff83f03f00ff0

def z778 : W := mkw 0x4801808610b4d0ce 0x14801808610b4d0c 0xa723838630fcf0cd 0xda723838630fcf0c

def z779 : W := mkw 0x04043229046284a8 0x004043229046284a 0x025472600ce38cf4 0x8025472600ce38cf

def z780 : W := mkw 0x803f6bfd80208088 0x7803f6bfd8020808 0xff3fffffc0e08000 0xbff3fffffc0e0800

def z781 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffc0fffff0007 0xc7f7ffc0fffff000

def z782 : W := mkw 0x4000800010900000 0x0400080001090000 0x3727838030fcb005 0xc3727838030fcb00

def z783 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffffffffcf00cf0b 0xfffffffffcf00cf0

def z784 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f3ffc0033ff0005 0x07f3ffc0033ff000

def z785 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdfdc72790ce38cfe 0xfdfdc72790ce38cf

def z786 : W := mkw 0x607add503fdb0000 0x6607add503fdb000 0xff7ffff03ffff00f 0xfff7ffff03ffff00

def z787 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8cf803f03f00ff0b 0x38cf803f03f00ff0

def z788 : W := mkw 0x503ac9503a902a00 0x6503ac9503a902a0 0xfffffff03ffcff0f 0xffffffff03ffcff0

def z789 : W := mkw 0x883d23ff8024d0ce 0x7883d23ff8024d0c 0x8f3803fff000f0c9 0xf8f3803fff000f0c

def z790 : W := mkw 0x04043229046284a8 0x004043229046284a 0x5bd472600ce38cfe 0xc5bd472600ce38cf

def z791 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7a7ffc003fff0006 0x87a7ffc003fff000

def z792 : W := mkw 0x4805a2af10b4d0ce 0x14805a2af10b4d0c 0xf727f38f30fcf0cd 0xdf727f38f30fcf0c

def z793 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8ff803ffff00ff0b 0xf8ff803ffff00ff0

def z794 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xbf2f839e30fcf0cd 0xfbf2f839e30fcf0c

def z795 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffc103fff4307 0xd7f7ffc103fff430

def z796 : W := mkw 0x80076bfd80000000 0x380076bfd8000000 0xfb17ffffc0000000 0x3fb17ffffc000000

def z797 : W := mkw 0x80076bfd80000000 0x380076bfd8000000 0x7007ffefc0000000 0x07007ffefc000000

def z798 : W := mkw 0x607adc0015db0000 0x4607adc0015db000 0x742ffc0000ff0004 0x0742ffc0000ff000

def z799 : W := mkw 0x803b488480000000 0x5803b48848000000 0x7f3ffc06c0000000 0x07f3ffc06c000000

def z800 : W := mkw 0x903f6bfdaa20aa88 0x7903f6bfdaa20aa8 0xffffffffffe0ffcf 0xfffffffffffe0ffc

def z801 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xffffffffff03ffff 0xfffffffffff03fff

def z802 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xfffffff93fffffff 0xffffffff93ffffff

def z803 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xaffffff6ff00ff0b 0xfaffffff6ff00ff0

def z804 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xffffffffcf008f0a 0xfffffffffcf008f0

def z805 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x785ffc003fff0007 0xc785ffc003fff000

def z806 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xf007fe6fc0000000 0x2f007fe6fc000000

def z807 : W := mkw 0x803f6bfd80208088 0x7803f6bfd8020808 0xffffffffcce08cce 0xfffffffffcce08cc

def z808 : W := mkw 0x4a05828e50b4d1df 0x14a05828e50b4d1d 0xbfaf839ff3fcf3ff 0xfbfaf839ff3fcf3f

def z809 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xffd80c1fcf1f43ff 0xfffd80c1fcf1f43f

def z810 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x9ff803f83f00ffcf 0xf9ff803f83f00ffc

def z811 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xffffffe03fffbc0f 0xeffffffe03fffbc0

def z812 : W := mkw 0x90076aadaa002a00 0x190076aadaa002a0 0x70c7fc0fff00ff0b 0xc70c7fc0fff00ff0

def z813 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xaff80ff6ff00ff0b 0xfaff80ff6ff00ff0

def z814 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xffaf8f9ff3fcf3cf 0xfffaf8f9ff3fcf3c

def z815 : W := mkw 0x403ac80010900000 0x4403ac8001090000 0x7f3ffc0000fc0004 0x07f3ffc0000fc000

def z816 : W := mkw 0x0002480000000000 0x0000248000000000 0x7007fc0fc0000000 0x07007fc0fc000000

def z817 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xfb37ffefc0000000 0x2fb37ffefc000000

def z818 : W := mkw 0x4805a2af10b4d0ce 0x14805a2af10b4d0c 0xfff7f3ef3cfcfccf 0xffff7f3ef3cfcfcc

def z819 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7907fc0000ff0006 0x47907fc0000ff000

def z820 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7d5ffc000fff0007 0x47d5ffc000fff000

def z821 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xfffffc703fff4f0f 0xffffffc703fff4f0

def z822 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffc16ffff0007 0xd7f7ffc16ffff000

def z823 : W := mkw 0x4c05828e10b4d4ee 0x14c05828e10b4d4e 0xb7a7838e30fcfcfd 0xdb7a7838e30fcfcf

def z824 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb7a7838e33fcf3cf 0xdb7a7838e33fcf3c

def z825 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x88d803f03f00ff0b 0xf88d803f03f00ff0

def z826 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xfd8ffc1fc300430b 0x7fd8ffc1fc300430

def z827 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xff2fff9fc0000000 0x3ff2fff9fc000000

def z828 : W := mkw 0x003a480000000000 0x4003a48000000000 0x7f3ffc0fc0000000 0x07f3ffc0fc000000

def z829 : W := mkw 0x6242dc0055db0111 0x06242dc0055db011 0x7007fc01c0ff0034 0x07007fc01c0ff003

def z830 : W := mkw 0x84076aad802084a8 0x184076aad802084a 0xf087fe6fc0008cf8 0x2f087fe6fc0008cf

def z831 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7257fc000cff0004 0x87257fc000cff000

def z832 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7ffffc103fff0307 0xe7ffffc103fff030

def z833 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3fffffc000f008 0x3ff3fffffc000f00

def z834 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xf727838f30fff0fd 0xdf727838f30fff0f

def z835 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x027003e03f00ff01 0x8027003e03f00ff0

def z836 : W := mkw 0x0c0522af0024d4ee 0x10c0522af0024d4e 0x8ff003ef3c00fcfb 0xf8ff003ef3c00fcf

def z837 : W := mkw 0x040532ad046294aa 0x1040532ad046294a 0xdbd473e90ce3bcfe 0xedbd473e90ce3bcf

def z838 : W := mkw 0x4c05a2af10b4d4ee 0x14c05a2af10b4d4e 0xffa783ef30fffcff 0xfffa783ef30fffcf

def z839 : W := mkw 0x6000940015db0000 0x06000940015db000 0x7f7ffc003fff0007 0xc7f7ffc003fff000

def z840 : W := mkw 0x607adc0015db0000 0x4607adc0015db000 0x7f3ffc0003ff0007 0x47f3ffc0003ff000

def z841 : W := mkw 0x0c0522af0024d4ee 0x10c0522af0024d4e 0x0000000f000000f0 0x00000000f000000f

def z842 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8ff803f93f00fffb 0xf8ff803f93f00fff

def z843 : W := mkw 0x407ad8003ed20000 0x4407ad8003ed2000 0x3f7ff0003ffc0007 0xc3f7ff0003ffc000

def z844 : W := mkw 0x6a7894027fdf4155 0x46a7894027fdf415 0x8ff800103fff43ff 0xf8ff800103fff43f

def z845 : W := mkw 0x6a40940255df4155 0x06a40940255df415 0x0080000003ff43ff 0x40080000003ff43f

def z846 : W := mkw 0x803f6bfd80208088 0x7803f6bfd8020808 0xffbfffffc0e380fe 0xfffbfffffc0e380f

def z847 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfd880e7fc31fcfff 0x7fd880e7fc31fcff

def z848 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x746ffc003fff0007 0xc746ffc003fff000

def z849 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3727818e30fc70c5 0xd3727818e30fc70c

def z850 : W := mkw 0xe045b7fdbfdb0000 0x3e045b7fdbfdb000 0x804003ffffff0007 0xf804003ffffff000

def z851 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x8227838e30fcf0cd 0xd8227838e30fcf0c

def z852 : W := mkw 0x803b49d480000000 0x7803b49d48000000 0x742ffd96c0000000 0x1742ffd96c000000

def z853 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x9ffc03f03fe0ff0f 0xf9ffc03f03fe0ff0

def z854 : W := mkw 0x627adc007fdb0111 0x4627adc007fdb011 0xfffffc19ffff03ff 0xefffffc19ffff03f

def z855 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xff8c0c1fc3ff43ff 0xfff8c0c1fc3ff43f

def z856 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb227838e30fcf0cc 0x9b227838e30fcf0c

def z857 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffd803fff7007 0xd7f7ffd803fff700

def z858 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x7b17fc0fc0000000 0x07b17fc0fc000000

def z859 : W := mkw 0xaa3f6fffc10d4155 0x7aa3f6fffc10d415 0x02b7f3e0031f43ff 0x402b7f3e0031f43f

def z860 : W := mkw 0x727add507fdb2b11 0x6727add507fdb2b1 0x7ffffc71ffff0f37 0xe7ffffc71ffff0f3

def z861 : W := mkw 0x647adc003fdb0420 0x4647adc003fdb042 0x7ffffc003fff0c37 0xc7ffffc003fff0c3

def z862 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xff27838e30fff0cf 0xdff27838e30fff0c

def z863 : W := mkw 0x803b69f580000000 0x7803b69f58000000 0xfd3bfdffc0000000 0x3fd3bfdffc000000

def z864 : W := mkw 0x903f6bfd80002a00 0x7903f6bfd80002a0 0xff3fffffc0007300 0x3ff3fffffc000730

def z865 : W := mkw 0x04003021046284a8 0x004003021046284a 0x48d070610ce30cf6 0x248d070610ce30cf

def z866 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xff7ffff03fff7307 0xfff7ffff03fff730

def z867 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x8727838030fcf0cd 0xd8727838030fcf0c

def z868 : W := mkw 0x607add503fdb0000 0x6607add503fdb000 0xfffffff03fff430f 0xffffffff03fff430

def z869 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffbfffffc00000f8 0x3ffbfffffc00000f

def z870 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xff7fff903ffff30f 0xdff7fff903ffff30

def z871 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x7c3ffdffc0000000 0x37c3ffdffc000000

def z872 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xa63fffffc0000000 0x3a63fffffc000000

def z873 : W := mkw 0x7a7acd527b9d6b55 0x67a7acd527b9d6b5 0x242b8d96f31c7301 0x1242b8d96f31c730

def z874 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffc11ffff0007 0xe7f7ffc11ffff000

def z875 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x84e803f03f00ff0b 0xf84e803f03f00ff0

def z876 : W := mkw 0xc805a2af90b4d0ce 0x1c805a2af90b4d0c 0xb727838ff0fcf0cd 0xdb727838ff0fcf0c

def z877 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3427818e30fcf0cd 0xd3427818e30fcf0c

def z878 : W := mkw 0x903b69f5aa002a00 0x7903b69f5aa002a0 0xeffbfff7ff00ff0b 0xfeffbfff7ff00ff0

def z879 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xff7fffffcc000c00 0x3ff7fffffcc000c0

def z880 : W := mkw 0x4000900014d20000 0x04000900014d2000 0x7727f00030ff0005 0xc7727f00030ff000

def z881 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xb73ffffec0000000 0x1b73ffffec000000

def z882 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7007fc0030ff0005 0xc7007fc0030ff000

def z883 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3fffffc0004009 0x7ff3fffffc000400

def z884 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xffaf8c1fc31f43ff 0x7ffaf8c1fc31f43f

def z885 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8f7803f03f00ff01 0xb8f7803f03f00ff0

def z886 : W := mkw 0x4805a2af10b4d0ce 0x14805a2af10b4d0c 0xff3ffffff0fcf0cd 0xfff3ffffff0fcf0c

def z887 : W := mkw 0x100001502a002a00 0x2100001502a002a0 0x00c003e03f00ff0b 0xc00c003e03f00ff0

def z888 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffbfffffc0004308 0x3ffbfffffc000430

def z889 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffc000fff0006 0x07f7ffc000fff000

def z890 : W := mkw 0x943f6bfd8020aea8 0x7943f6bfd8020aea 0xffbfffffc000fff8 0x3ffbfffffc000fff

def z891 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0x7277ffeffc00bc00 0x87277ffeffc00bc0

def z892 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x780ffc1fc0000000 0x2780ffc1fc000000

def z893 : W := mkw 0x4800800210b4d0ce 0x04800800210b4d0c 0xb727838030fcf0cd 0xdb727838030fcf0c

def z894 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdff472693ce38cff 0xedff472693ce38cf

def z895 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffc093fff00f7 0xc7f7ffc093fff00f

def z896 : W := mkw 0x627adc007fdb0111 0x4627adc007fdb011 0x7f7ffc10ffff0307 0xc7f7ffc10ffff030

def z897 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x763fffffc0000000 0x1763fffffc000000

def z898 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfd880f9fc31ff3ff 0x7fd880f9fc31ff3f

def z899 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xffaf839f33fff3ff 0xfffaf839f33fff3f

def z900 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x5b77f0003fff0007 0xc5b77f0003fff000

def z901 : W := mkw 0x80076bfd80000000 0x380076bfd8000000 0xf727ffffc0000000 0x3f727ffffc000000

def z902 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdbf473e93ce3bcfe 0xedbf473e93ce3bcf

def z903 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb727838e30fcf001 0x9b727838e30fcf00

def z904 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb7a7838e30fff0ff 0xdb7a7838e30fff0f

def z905 : W := mkw 0x0c0522af0024d4ee 0x10c0522af0024d4e 0x800003ee0000fcc8 0x1800003ee0000fcc

def z906 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xff3ffffff300f309 0xfff3ffffff300f30

def z907 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffc003ffff00f 0xc7f7ffc003ffff00

def z908 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3fffffc0e00004 0xfff3fffffc0e0000

def z909 : W := mkw 0x803f6bfd80208088 0x7803f6bfd8020808 0xff3ffffff0e0f0cd 0xfff3ffffff0e0f0c

def z910 : W := mkw 0x707adc003fdb2a00 0x4707adc003fdb2a0 0x7f7ffc003fff7307 0xc7f7ffc003fff730

def z911 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xff7ffffffc00fc09 0xfff7ffffffc00fc0

def z912 : W := mkw 0x04003021046284a8 0x004003021046284a 0xd9d070690ce38cfe 0xed9d070690ce38cf

def z913 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xfffffffffc00ff08 0xbfffffffffc00ff0

def z914 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3727838e30fcb0c5 0xc3727838e30fcb0c

def z915 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xf81fffffc0000000 0x3f81fffffc000000

def z916 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0af803f03f00ff0b 0xe0af803f03f00ff0

def z917 : W := mkw 0x307a5d502f4b2a00 0x6307a5d502f4b2a0 0x48587c600f030c02 0x048587c600f030c0

def z918 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x7227ff8fc0000000 0x07227ff8fc000000

def z919 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb527818e30fc70cd 0x5b527818e30fc70c

def z920 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7f7ffff03fffff07 0xd7f7ffff03fffff0

def z921 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x7007fc0fc00300f4 0x07007fc0fc00300f

def z922 : W := mkw 0x607acc003b990000 0x4607acc003b99000 0x7f3ffc0033fc0005 0xc7f3ffc0033fc000

def z923 : W := mkw 0x8c0523ff8024d4ee 0x38c0523ff8024d4e 0x808003ffc000fcf8 0x3808003ffc000fcf

def z924 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x242ffd96c0000000 0x1242ffd96c000000

def z925 : W := mkw 0x7a4094027fdf6b55 0x07a4094027fdf6b5 0x00c000003fffffff 0xc00c000003ffffff

def z926 : W := mkw 0x903f6bfd80002a00 0x7903f6bfd80002a0 0xffbfffffc0000f00 0x3ffbfffffc0000f0

def z927 : W := mkw 0x003e6a2900000000 0x4003e6a290000000 0xff3ffe7fc0000000 0x3ff3ffe7fc000000

def z928 : W := mkw 0x7042dd5015db2a00 0x27042dd5015db2a0 0xf087fff000ffff0c 0x3f087fff000ffff0

def z929 : W := mkw 0x4004820810b08088 0x04004820810b0808 0xb727838830fcf0cd 0xdb727838830fcf0c

def z930 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0xfd0ffc1fc0ff0004 0x3fd0ffc1fc0ff000

def z931 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0ff803e03f00ff0b 0xc0ff803e03f00ff0

def z932 : W := mkw 0x4005828c10900000 0x14005828c1090000 0xb727838e30fcf00d 0xdb727838e30fcf00

def z933 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfd880c1fc31f03f6 0x3fd880c1fc31f03f

def z934 : W := mkw 0x607add5015db0000 0x6607add5015db000 0xff3ffff000ff0004 0x3ff3ffff000ff000

def z935 : W := mkw 0x04003021046284a8 0x004003021046284a 0xcbd072610ce38cfe 0xecbd072610ce38cf

def z936 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x0227838030fcb0c4 0x80227838030fcb0c

def z937 : W := mkw 0x287f5e8e2f6fd0ce 0x5287f5e8e2f6fd0c 0xc8587f8e0f03f0ca 0x1c8587f8e0f03f0c

def z938 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7b17fc0000ff0004 0x07b17fc0000ff000

def z939 : W := mkw 0x4801808610b4d0ce 0x14801808610b4d0c 0x2423818630fcf001 0x92423818630fcf00

def z940 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3fffffc3004301 0x3ff3fffffc300430

def z941 : W := mkw 0x203a5c00054b0000 0x4203a5c00054b000 0x7f7ffc000fff0007 0xc7f7ffc000fff000

def z942 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfd880c1ff31ff3ff 0xffd880c1ff31ff3f

def z943 : W := mkw 0x4801808610945046 0x1480180861094504 0x3427818630fc7005 0x13427818630fc700

def z944 : W := mkw 0x003a48002a000000 0x4003a48002a00000 0xfffffc1fff00430b 0xffffffc1fff00430

def z945 : W := mkw 0x040532ad046284a8 0x1040532ad046284a 0xfbd7f26f0ce38cfe 0xefbd7f26f0ce38cf

def z946 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xa423838e30fcf0cd 0xda423838e30fcf0c

def z947 : W := mkw 0x843f6bfd802084a8 0x7843f6bfd802084a 0xffbfffffc0e08cfc 0xfffbfffffc0e08cf

def z948 : W := mkw 0x84076aad802084a8 0x184076aad802084a 0x7007fc0fc00000f0 0x07007fc0fc00000f

def z949 : W := mkw 0x903f6bfd80002a00 0x7903f6bfd80002a0 0xff3fffffc000bc00 0x3ff3fffffc000bc0

def z950 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x0277f0003ffc0001 0x80277f0003ffc000

def z951 : W := mkw 0x04001000046284a8 0x004001000046284a 0xdbd472600ce38cfe 0xedbd472600ce38cf

def z952 : W := mkw 0x6042dc003fdb0000 0x06042dc003fdb000 0x7047fc003cff0004 0x87047fc003cff000

def z953 : W := mkw 0x627adc007fdb0111 0x4627adc007fdb011 0xfffffc1fffff0337 0xffffffc1fffff033

def z954 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x9327838830fcf0cd 0xc9327838830fcf0c

def z955 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7d2ffc0033ff0007 0x47d2ffc0033ff000

def z956 : W := mkw 0x100001502a002a00 0x2100001502a002a0 0x8dc803f03f00ff0b 0xf8dc803f03f00ff0

def z957 : W := mkw 0x880523ff8024d0ce 0x3880523ff8024d0c 0x800003ffc00000c0 0x3800003ffc00000c

def z958 : W := mkw 0x04043229046284a8 0x004043229046284a 0x93d472680ce38cfe 0xc93d472680ce38cf

def z959 : W := mkw 0x407ad8003ed20000 0x4407ad8003ed2000 0x7f7ffc003cfc0005 0xc7f7ffc003cfc000

def z960 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x8ffff3f03fffff0f 0xf8ffff3f03fffff0

def z961 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xa727838630fcf009 0xda727838630fcf00

def z962 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xff3fffffc3000300 0x3ff3fffffc300030

def z963 : W := mkw 0x880522af8024d0ce 0x1880522af8024d0c 0x8000038fc000f0c8 0x18000038fc000f0c

def z964 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7227fc0030ff0004 0x87227fc0030ff000

def z965 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffc003ffc0001 0x87f7ffc003ffc000

def z966 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0xb727838030fcf00d 0xdb727838030fcf00

def z967 : W := mkw 0x0000100004420000 0x0000010000442000 0xdbd472690ce38cfe 0xedbd472690ce38cf

def z968 : W := mkw 0x403ac8003a900000 0x4403ac8003a90000 0x7f7ffc003ffc0007 0xc7f7ffc003ffc000

def z969 : W := mkw 0x803f6bfd80208088 0x7803f6bfd8020808 0xff3fffffc0e000c4 0x3ff3fffffc0e000c

def z970 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdff473e90ce38cfe 0xfdff473e90ce38cf

def z971 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb77783ee3cfcfccd 0xdb77783ee3cfcfcc

def z972 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xffbffffff300ff09 0x3ffbffffff300ff0

def z973 : W := mkw 0x507ad9503ed22a00 0x6507ad9503ed22a0 0xbffff3f03ffcff0f 0xfbffff3f03ffcff0

def z974 : W := mkw 0x903f6bfd80002a00 0x7903f6bfd80002a0 0xffbffffff000ff09 0xfffbffffff000ff0

def z975 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7ffffff03fffbf07 0xe7ffffff03fffbf0

def z976 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xec880c1fc31f43fb 0x3ec880c1fc31f43f

def z977 : W := mkw 0x803f6bfd80208088 0x7803f6bfd8020808 0xff3fffffc00080c8 0x3ff3fffffc00080c

def z978 : W := mkw 0x04043229046284a8 0x004043229046284a 0x52d472690ce38cfe 0xc52d472690ce38cf

def z979 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xff7fffffff00ff01 0xbff7fffffff00ff0

def z980 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xaffffff03ffcff0b 0xfaffffff03ffcff0

def z981 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x7727fc0fc0000000 0x07727fc0fc000000

def z982 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x267ffff03ffcff01 0x9267ffff03ffcff0

def z983 : W := mkw 0x4001808410901002 0x1400180841090100 0x3727818030fc3005 0xc3727818030fc300

def z984 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x4a7ffc003fff0007 0xc4a7ffc003fff000

def z985 : W := mkw 0x04043229046284a8 0x004043229046284a 0x5bd470690ce30cf6 0xe5bd470690ce30cf

def z986 : W := mkw 0x80076bfd80000000 0x380076bfd8000000 0x7007fc7fc0000000 0x27007fc7fc000000

def z987 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffbfffffc0008c08 0x3ffbfffffc0008c0

def z988 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xff7ffc083fff00cf 0xcff7ffc083fff00c

def z989 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x0f7ff0003fff0007 0xc0f7ff0003fff000

def z990 : W := mkw 0x4042d80014d20000 0x04042d80014d2000 0x3007f00000fc0004 0x03007f00000fc000

def z991 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb7a783ee30fcfccd 0xfb7a783ee30fcfcc

def z992 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x6e3ffff7c0000000 0x36e3ffff7c000000

def z993 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7727fc0000ff0004 0x07727fc0000ff000

def z994 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7f7ffc603fff0c07 0xc7f7ffc603fff0c0

def z995 : W := mkw 0x3a3805526b0d6b55 0x63a3805526b0d6b5 0x72700feffc1fbcf4 0x872700feffc1fbcf

def z996 : W := mkw 0x803f6aad80000000 0x5803f6aad8000000 0x781ffc0fc0000000 0x0781ffc0fc000000

def z997 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x06f803f03f00ff0b 0xd06f803f03f00ff0

def z998 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xfffffe703fffcf0f 0xffffffe703fffcf0

def z999 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xf7278f8ff0fcf0cd 0xdf7278f8ff0fcf0c

def z1000 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x7f3ffff6c0000000 0x17f3ffff6c000000

def z1001 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x2f7ffc003ffc0003 0xc2f7ffc003ffc000

def z1002 : W := mkw 0x04043229046284a8 0x004043229046284a 0xd9d470690ce30cfe 0x6d9d470690ce30cf

def z1003 : W := mkw 0x803f4bdc80000000 0x7803f4bdc8000000 0xff3fff9ec0000000 0x1ff3fff9ec000000

def z1004 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7507fc0000ff0005 0x47507fc0000ff000

def z1005 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x2007fc0000fc0000 0x02007fc0000fc000

def z1006 : W := mkw 0x8003488480000000 0x1800348848000000 0x7007fc06c0000000 0x07007fc06c000000

def z1007 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7047fc000cff0006 0xc7047fc000cff000

def z1008 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xfbd7fe6fcc008c0a 0xefbd7fe6fcc008c0

def z1009 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7ffffc003fff430f 0xc7ffffc003fff430

def z1010 : W := mkw 0x803f6aad80000000 0x5803f6aad8000000 0xff3fff8fc0000000 0x1ff3fff8fc000000

def z1011 : W := mkw 0x040532ad046284a8 0x1040532ad046284a 0xfff7f3ef3ce3fcff 0xffff7f3ef3ce3fcf

def z1012 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3fffffc0008008 0xfff3fffffc000800

def z1013 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffbfffffc30343ff 0x7ffbfffffc30343f

def z1014 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xf8880c1fc31f43fe 0x3f8880c1fc31f43f

def z1015 : W := mkw 0x003f4a8c00000000 0x5003f4a8c0000000 0xff3fff9fc0000000 0x3ff3fff9fc000000

def z1016 : W := mkw 0x503891503ed22a00 0x6503891503ed22a0 0xfffff3f03fffff0f 0xffffff3f03fffff0

def z1017 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdb5472690ce38cf4 0xadb5472690ce38cf

def z1018 : W := mkw 0x803b69f580000000 0x7803b69f58000000 0x642bfd97c0000000 0x1642bfd97c000000

def z1019 : W := mkw 0x307a5d502f4b2a00 0x6307a5d502f4b2a0 0x48587c100f030302 0x048587c100f03030

def z1020 : W := mkw 0x4800800210944044 0x0480080021094404 0xb727838e30fcf0cd 0xdb727838e30fcf0c

def z1021 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xcff80ff1ff00ff0b 0xfcff80ff1ff00ff0

def z1022 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xf307fe0fc0000000 0x0f307fe0fc000000

def z1023 : W := mkw 0x880522af8024d0ce 0x1880522af8024d0c 0x0000000fc00000c0 0x00000000fc00000c

def z1024 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xfffffe693fff8cff 0xefffffe693fff8cf

def z1025 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xffbffffff300730b 0x7ffbffffff300730

def z1026 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7007fc0fc0ff0004 0x07007fc0fc0ff000

def z1027 : W := mkw 0x880523ff8024d0ce 0x3880523ff8024d0c 0x800003ee0000f0c8 0x1800003ee0000f0c

def z1028 : W := mkw 0x4000800010900000 0x0400080001090000 0x3727818030fc7005 0xd3727818030fc700

def z1029 : W := mkw 0x4042d80014d20000 0x04042d80014d2000 0x3727f00030fc0005 0xc3727f00030fc000

def z1030 : W := mkw 0x607add503fdb0000 0x6607add503fdb000 0x7f7ffd903fff0007 0xd7f7ffd903fff000

def z1031 : W := mkw 0x4801808610b4d0ce 0x14801808610b4d0c 0x2423818630fc70c5 0x12423818630fc70c

def z1032 : W := mkw 0x6e05b6af55ffd5ff 0x16e05b6af55ffd5f 0x7007fc0fc0ff00f4 0x07007fc0fc0ff00f

def z1033 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xbf2f838e33fcf0cf 0xdbf2f838e33fcf0c

def z1034 : W := mkw 0x4a05828e50b4d1df 0x14a05828e50b4d1d 0xffa7839ff0fff3ff 0xfffa7839ff0fff3f

def z1035 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffbfffffc000000a 0x7ffbfffffc000000

def z1036 : W := mkw 0x607add503fdb0000 0x6607add503fdb000 0x7f7fffe03fff0007 0xc7f7fffe03fff000

def z1037 : W := mkw 0x803f6bfdaa000000 0x7803f6bfdaa00000 0xff7fffffcf000002 0x3ff7fffffcf00000

def z1038 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xbfff83fe3ffcffcf 0xfbfff83fe3ffcffc

def z1039 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xff7fff803fff0007 0xdff7fff803fff000

def z1040 : W := mkw 0x803b69f580000000 0x7803b69f58000000 0x681bfc77c0000000 0x2681bfc77c000000

def z1041 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffffffffcc038cfe 0xfffffffffcc038cf

def z1042 : W := mkw 0x4002c80010900000 0x04002c8001090000 0x7727fc0030fc0005 0xc7727fc0030fc000

def z1043 : W := mkw 0x04043229046284a8 0x004043229046284a 0x58d470690ce38cfe 0xe58d470690ce38cf

def z1044 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xa4880c1fc31f43ff 0x7a4880c1fc31f43f

def z1045 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0x2627838030fcb001 0x82627838030fcb00

def z1046 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xff880e1fc31fc3ff 0xfff880e1fc31fc3f

def z1047 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xaf3ffff6c0000000 0x3af3ffff6c000000

def z1048 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7777fc003cff0005 0xc7777fc003cff000

def z1049 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xf9880c1fc31f03fe 0x6f9880c1fc31f03f

def z1050 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xfd1ffc7fc0000000 0x3fd1ffc7fc000000

def z1051 : W := mkw 0x803b69f580000000 0x7803b69f58000000 0xef3bfff7c0000000 0x3ef3bfff7c000000

def z1052 : W := mkw 0x803f6bfdaa000000 0x7803f6bfdaa00000 0xffffffffff00430b 0xfffffffffff00430

def z1053 : W := mkw 0x4801808610945046 0x1480180861094504 0x2627818630fc7001 0x92627818630fc700

def z1054 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xf987fc0fc00300fe 0x6f987fc0fc00300f

def z1055 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xffffffe03ffffc0f 0xfffffffe03ffffc0

def z1056 : W := mkw 0x040532ad046284a8 0x1040532ad046284a 0xdbf7f3e90ce38cfe 0xedbf7f3e90ce38cf

def z1057 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdbd472690fe3cfff 0xedbd472690fe3cff

def z1058 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xfffffffffc00bc0a 0xffffffffffc00bc0

def z1059 : W := mkw 0x003a495000000000 0x6003a49500000000 0xff3fffffc0000000 0x3ff3fffffc000000

def z1060 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0xf987fc0900ff00fe 0x6f987fc0900ff00f

def z1061 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff7fffffcc008c00 0xbff7fffffcc008c0

def z1062 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7007fc0900ff00f4 0x07007fc0900ff00f

def z1063 : W := mkw 0x04043229046284a8 0x004043229046284a 0x4ad472610ce38cfe 0xe4ad472610ce38cf

def z1064 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x0007f00000ff0004 0x00007f00000ff000

def z1065 : W := mkw 0x707adc003fdb2a00 0x4707adc003fdb2a0 0xffffff803fffff0f 0xdffffff803fffff0

def z1066 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x2237ffe6c0000000 0x02237ffe6c000000

def z1067 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xffaf8f9ff0fff0ff 0xfffaf8f9ff0fff0f

def z1068 : W := mkw 0x4801808610b4d0ce 0x14801808610b4d0c 0x0023818030fcf0cd 0xc0023818030fcf0c

def z1069 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x7017fc6fc0000000 0x07017fc6fc000000

def z1070 : W := mkw 0x04043229046284a8 0x004043229046284a 0xfbd47e6fcce38cfe 0xefbd47e6fcce38cf

def z1071 : W := mkw 0x803f6bfdaa000000 0x7803f6bfdaa00000 0xff7fffffff00f00b 0xfff7fffffff00f00

def z1072 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfd080c1fc31f43f5 0x3fd080c1fc31f43f

def z1073 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xf907fc0fc0000000 0x2f907fc0fc000000

def z1074 : W := mkw 0x6042dc003fdb0000 0x06042dc003fdb000 0x7b57fc003fff0007 0xc7b57fc003fff000

def z1075 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xff7ffc0e3fff0007 0xdff7ffc0e3fff000

def z1076 : W := mkw 0x803b49d480000000 0x7803b49d48000000 0x263ffd96c0000000 0x1263ffd96c000000

def z1077 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x6e7ffc003fff0003 0x86e7ffc003fff000

def z1078 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xfffffd903fff730f 0xffffffd903fff730

def z1079 : W := mkw 0x6042dc003fdb0000 0x06042dc003fdb000 0x7007fc0033ff0005 0x07007fc0033ff000

def z1080 : W := mkw 0x803f6aadaa000000 0x5803f6aadaa00000 0x7f7ffc0fff000003 0xc7f7ffc0fff00000

def z1081 : W := mkw 0x4c05a2af10b4d4ee 0x14c05a2af10b4d4e 0xffb7f3ef30fcfcfd 0xfffb7f3ef30fcfcf

def z1082 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7ffffc003fff00ff 0xc7ffffc003fff00f

def z1083 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xfffffc1fffff430f 0xffffffc1fffff430

def z1084 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7fffffe03fffff0f 0xc7fffffe03fffff0

def z1085 : W := mkw 0x4805a2af10b4d0ce 0x14805a2af10b4d0c 0xffb7f3ef30fff0ff 0xfffb7f3ef30fff0f

def z1086 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xffffffffff007f03 0x3ffffffffff007f0

def z1087 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xf737ffefc0000000 0x1f737ffefc000000

def z1088 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x242ffc0033fc0001 0x0242ffc0033fc000

def z1089 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xbff803fe3f00ff0b 0xfbff803fe3f00ff0

def z1090 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x2007fc06c0000000 0x02007fc06c000000

def z1091 : W := mkw 0x103a49502a002a00 0x6103a49502a002a0 0xcff87ff03f00ff0b 0xfcff87ff03f00ff0

def z1092 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7b5ffc000fff0006 0xc7b5ffc000fff000

def z1093 : W := mkw 0x607add503fdb0000 0x6607add503fdb000 0x7f7ffc703fff0007 0xe7f7ffc703fff000

def z1094 : W := mkw 0x080522af0024d0ce 0x1080522af0024d0c 0x800003ef0000f0c8 0x3800003ef0000f0c

def z1095 : W := mkw 0x4c05a2af10b4d4ee 0x14c05a2af10b4d4e 0xbff783ef3cfcfcff 0xfbff783ef3cfcfcf

def z1096 : W := mkw 0x803a697180000000 0x6803a69718000000 0xff3ffc7fc0000000 0x3ff3ffc7fc000000

def z1097 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffffffffcc000c02 0x3ffffffffcc000c0

def z1098 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xff7ffc103fff0007 0xfff7ffc103fff000

def z1099 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xf727ff8ff000f009 0xdf727ff8ff000f00

def z1100 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x7f3ffd9fc0000000 0x17f3ffd9fc000000

def z1101 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xff7ffe603fff0007 0xeff7ffe603fff000

def z1102 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xff7ffe003fff800f 0xcff7ffe003fff800

def z1103 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x772ffc0033ff0005 0xc772ffc0033ff000

def z1104 : W := mkw 0x4a05828e50b4d1df 0x14a05828e50b4d1d 0xb727838ff0fcf0fd 0xdb727838ff0fcf0f

def z1105 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb7a7838f30fcf0fd 0xfb7a7838f30fcf0f

def z1106 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x0277f0003cff0004 0x80277f0003cff000

def z1107 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xec3bffffc0000000 0x3ec3bffffc000000

def z1108 : W := mkw 0x803f6aad80000000 0x5803f6aad8000000 0x742ffc0fc0000000 0x0742ffc0fc000000

def z1109 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3fffffc00000cc 0x7ff3fffffc00000c

def z1110 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xff37f38e30fcf0cd 0xdff37f38e30fcf0c

def z1111 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xff7fffffff007303 0xfff7fffffff00730

def z1112 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7ffffc703fffff0f 0xe7ffffc703fffff0

def z1113 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xff9c7c1fc31f43ff 0x7ff9c7c1fc31f43f

def z1114 : W := mkw 0x04043229046284a8 0x004043229046284a 0xcad472690ce38cfa 0xacad472690ce38cf

def z1115 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb72f839e33fcf3cd 0xdb72f839e33fcf3c

def z1116 : W := mkw 0x040532ad046284a8 0x1040532ad046284a 0xdbd473ef0ce38cfe 0xfdbd473ef0ce38cf

def z1117 : W := mkw 0x707adc003fdb2a00 0x4707adc003fdb2a0 0xfffffc103fffff0f 0xffffffc103fffff0

def z1118 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xbf77838e3cfcf0cf 0xdbf77838e3cfcf0c

def z1119 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x78dffc700fff0f06 0x278dffc700fff0f0

def z1120 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3627838e30fcf0c5 0x93627838e30fcf0c

def z1121 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff7fffffcc000002 0xfff7fffffcc00000

def z1122 : W := mkw 0x04043229046284a8 0x004043229046284a 0xffdc7e7fcfe3cfff 0xfffdc7e7fcfe3cff

def z1123 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7277ffe03cffbc04 0x87277ffe03cffbc0

def z1124 : W := mkw 0x6042dc003fdb0000 0x06042dc003fdb000 0x7767fc003fff0007 0xc7767fc003fff000

def z1125 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7057fc000cff0004 0x07057fc000cff000

def z1126 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffbffffff300f30b 0xfffbffffff300f30

def z1127 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfdc80c1fcf1fcfff 0xffdc80c1fcf1fcff

def z1128 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8bf003e03f00ff0b 0xe8bf003e03f00ff0

def z1129 : W := mkw 0x707adc003fdb2a00 0x4707adc003fdb2a0 0xfffffe603fffff0f 0xefffffe603fffff0

def z1130 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xf42fffffc0000000 0x3f42fffffc000000

def z1131 : W := mkw 0x4801808610b4d0ce 0x14801808610b4d0c 0xb523818e30fcf0cd 0xdb523818e30fcf0c

def z1132 : W := mkw 0x4c05a2af10b4d4ee 0x14c05a2af10b4d4e 0xb72783ee30fcfccd 0xdb72783ee30fcfcc

def z1133 : W := mkw 0x6a40940255df4155 0x06a40940255df415 0x0000000000ff00f4 0x00000000000ff00f

def z1134 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdffc73f93fe3ffff 0xfdffc73f93fe3fff

def z1135 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xff7ffc093fff0007 0xeff7ffc093fff000

def z1136 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xfffffffffc00fc0b 0xffffffffffc00fc0

def z1137 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x02f7f3e03fffff0f 0xc02f7f3e03fffff0

def z1138 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffbfffffc0030032 0x3ffbfffffc003003

def z1139 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0xfbd7fe600cff8c0e 0xefbd7fe600cff8c0

def z1140 : W := mkw 0x04043229046284a8 0x004043229046284a 0xffd4726f0ce38cfe 0xfffd4726f0ce38cf

def z1141 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7007fc0003ff0007 0x47007fc0003ff000

def z1142 : W := mkw 0x607adc0015db0000 0x4607adc0015db000 0x7237fc0000ff0004 0x07237fc0000ff000

def z1143 : W := mkw 0x4801808610945046 0x1480180861094504 0xb727838630fcf00d 0xdb727838630fcf00

def z1144 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdbd4727fcce38cfe 0xfdbd4727fcce38cf

def z1145 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7ffffdf03fff7f07 0xf7ffffdf03fff7f0

def z1146 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xbfa7838e30fcf0cf 0xfbfa7838e30fcf0c

def z1147 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x7f3fffefc0000000 0x07f3fffefc000000

def z1148 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7ffffd903fffff0f 0xd7ffffd903fffff0

def z1149 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0x0227838030fcb005 0xc0227838030fcb00

def z1150 : W := mkw 0x4c05a2af10b4d4ee 0x14c05a2af10b4d4e 0xb727838f30fcf0fd 0xdb727838f30fcf0f

def z1151 : W := mkw 0x627adc007fdb0111 0x4627adc007fdb011 0xfffffc11ffff433f 0xffffffc11ffff433

def z1152 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xff27838f30fcf0cd 0xfff27838f30fcf0c

def z1153 : W := mkw 0x4000900014d20000 0x04000900014d2000 0x3777f0003cfc0005 0xc3777f0003cfc000

def z1154 : W := mkw 0x943f6bfdaa20aea8 0x7943f6bfdaa20aea 0xffffffffff00fffb 0xfffffffffff00fff

def z1155 : W := mkw 0x103a49502a002a00 0x6103a49502a002a0 0xaffb8ff03f00ff0b 0xfaffb8ff03f00ff0

def z1156 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xf237ffffc0000000 0x3f237ffffc000000

def z1157 : W := mkw 0x403ac80010900000 0x4403ac8001090000 0x3737f00030fc0005 0xc3737f00030fc000

def z1158 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xff2f8f8e30fcf0cd 0xdff2f8f8e30fcf0c

def z1159 : W := mkw 0x843f6bfd802084a8 0x7843f6bfd802084a 0xffffffffcc008cfa 0xfffffffffcc008cf

def z1160 : W := mkw 0x327a5d506f4b2b11 0x6327a5d506f4b2b1 0x48d87c71cf030f32 0x248d87c71cf030f3

def z1161 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfdd80c7fcf1f4fff 0x7fdd80c7fcf1f4ff

def z1162 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffe603fff8c07 0xc7f7ffe603fff8c0

def z1163 : W := mkw 0x04043229046284a8 0x004043229046284a 0xfff7f2690ce38cfe 0xefff7f2690ce38cf

def z1164 : W := mkw 0x4a05828e50b4d1df 0x14a05828e50b4d1d 0xb7a7838e30fcf3fd 0xdb7a7838e30fcf3f

def z1165 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7c7ffc003fff0007 0x07c7ffc003fff000

def z1166 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x740ffc1fc0000000 0x1740ffc1fc000000

def z1167 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdbd472790ce3cffe 0xfdbd472790ce3cff

def z1168 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdbd472693ce3fcff 0xedbd472693ce3fcf

def z1169 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x8af803f03f00ff0a 0xb8af803f03f00ff0

def z1170 : W := mkw 0x903a4950aa002a00 0x6903a4950aa002a0 0x8ff80ff0ff00ff0b 0xf8ff80ff0ff00ff0

def z1171 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x7427fd8fc0000000 0x17427fd8fc000000

def z1172 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3fffffc3000003 0x7ff3fffffc300000

def z1173 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xffffff903ffff30f 0xfffffff903ffff30

def z1174 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xff980e7fc31f43ff 0x7ff980e7fc31f43f

def z1175 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7b77fc003cff0006 0xc7b77fc003cff000

def z1176 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb727838e30fc70c5 0x1b727838e30fc70c

def z1177 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3027818e30fc30c4 0x03027818e30fc30c

def z1178 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xffbfffffc3000302 0x3ffbfffffc300030

def z1179 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3227838e30fcf0cd 0xc3227838e30fcf0c

def z1180 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x2627838630fcf0cd 0xd2627838630fcf0c

def z1181 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7f5ffc000fff0007 0xc7f5ffc000fff000

def z1182 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x700ffc0003ff0004 0x0700ffc0003ff000

def z1183 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xffffffffff000f03 0xfffffffffff000f0

def z1184 : W := mkw 0x7042dc003fdb2a00 0x07042dc003fdb2a0 0x70c7fc003fffff0f 0xc70c7fc003fffff0

def z1185 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7f7ffc103fff0307 0xc7f7ffc103fff030

def z1186 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7d0ffc0000ff0004 0x07d0ffc0000ff000

def z1187 : W := mkw 0x103a49502a002a00 0x6103a49502a002a0 0x8ffff3f03f00ff0b 0xf8ffff3f03f00ff0

def z1188 : W := mkw 0x1c0523ff0024feee 0x31c0523ff0024fee 0x808003ff0000fff8 0x3808003ff0000fff

def z1189 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xdff803f03f03ff0f 0xfdff803f03f03ff0

def z1190 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xff7ffc003fff400f 0xdff7ffc003fff400

def z1191 : W := mkw 0x603acc0011990000 0x4603acc001199000 0x7f3ffc0033ff0007 0xc7f3ffc0033ff000

def z1192 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7277fc003fff0007 0xc7277fc003fff000

def z1193 : W := mkw 0x403ac95010900000 0x6403ac9501090000 0xff3ffff030fcf00d 0xfff3ffff030fcf00

def z1194 : W := mkw 0x507ad9503ed22a00 0x6507ad9503ed22a0 0xb777f3e03cfcfc0d 0xdb777f3e03cfcfc0

def z1195 : W := mkw 0x04043229046284a8 0x004043229046284a 0xffd472690cff8cff 0xeffd472690cff8cf

def z1196 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x3777f0003fff0007 0xc3777f0003fff000

def z1197 : W := mkw 0x4000800010900000 0x0400080001090000 0x7f37f00030fc0005 0xc7f37f00030fc000

def z1198 : W := mkw 0x803f6aad80000000 0x5803f6aad8000000 0xff3ffc1fc0000000 0x3ff3ffc1fc000000

def z1199 : W := mkw 0x347a7d712f4b2e20 0x6347a7d712f4b2e2 0x48d87c710f030f32 0x248d87c710f030f3

def z1200 : W := mkw 0x903b49d4aa002a00 0x7903b49d4aa002a0 0xfffffff6ff00ff0b 0xffffffff6ff00ff0

def z1201 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xff7fffffff00bc03 0xfff7fffffff00bc0

def z1202 : W := mkw 0x6042dc003fdb0000 0x06042dc003fdb000 0x7047fc000fff0006 0x07047fc000fff000

def z1203 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x2227838630fcb000 0x82227838630fcb00

def z1204 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xffffffffff00bf02 0xbffffffffff00bf0

def z1205 : W := mkw 0x803b69f580000000 0x7803b69f58000000 0x243bfdf6c0000000 0x1243bfdf6c000000

def z1206 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xff1ffe7fc0000000 0x3ff1ffe7fc000000

def z1207 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xff37ffefc0000000 0x3ff37ffefc000000

def z1208 : W := mkw 0x407ad8003ed20000 0x4407ad8003ed2000 0x2677f0003cfc0001 0x82677f0003cfc000

def z1209 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb427838e30fcf0cd 0x1b427838e30fcf0c

def z1210 : W := mkw 0x4000900014d20000 0x04000900014d2000 0xfff7f3e03cfffc0f 0xffff7f3e03cfffc0

def z1211 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xfff80fffff03ffff 0xffff80fffff03fff

def z1212 : W := mkw 0x803f6aad80000000 0x5803f6aad8000000 0x7237fc0fc0000000 0x07237fc0fc000000

def z1213 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3fffffc00300f4 0x3ff3fffffc00300f

def z1214 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x2277fc003cfc0000 0x82277fc003cfc000

def z1215 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xcff803f13f03ff3b 0xfcff803f13f03ff3

def z1216 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xf007ff8fc0000000 0x1f007ff8fc000000

def z1217 : W := mkw 0x983d23ffaa24face 0x7983d23ffaa24fac 0x8ff803ffff00ffcb 0xf8ff803ffff00ffc

def z1218 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x7217fe6fc0000000 0x07217fe6fc000000

def z1219 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x7d080c1fc31f43f7 0x57d080c1fc31f43f

def z1220 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdfd472690ce3ccff 0xfdfd472690ce3ccf

def z1221 : W := mkw 0x803f6bfdaa000000 0x7803f6bfdaa00000 0xffffffffff008c0b 0xfffffffffff008c0

def z1222 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xff3ffffff0003000 0x3ff3ffffff000300

def z1223 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x377ffc003ffc0005 0xc377ffc003ffc000

def z1224 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdbd473e90ce3fcfe 0xfdbd473e90ce3fcf

def z1225 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x7c880c1fc31f43f7 0x37c880c1fc31f43f

def z1226 : W := mkw 0x803f6aad80000000 0x5803f6aad8000000 0xff3ffe6fc0000000 0x2ff3ffe6fc000000

def z1227 : W := mkw 0x607adc0015db0000 0x4607adc0015db000 0x7f3ffc0030ff0005 0xc7f3ffc0030ff000

def z1228 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xf5080c1fc31f43fd 0x5f5080c1fc31f43f

def z1229 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7ffffc013fff0037 0xe7ffffc013fff003

def z1230 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0xb727838830fcb0cd 0xcb727838830fcb0c

def z1231 : W := mkw 0x607add503fdb0000 0x6607add503fdb000 0xfffffff03fff8c0f 0xffffffff03fff8c0

def z1232 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xff7ffff03fffbc07 0xfff7ffff03fffbc0

def z1233 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xbff803f03f1cff0f 0xfbff803f03f1cff0

def z1234 : W := mkw 0x7a7895527fdf6b55 0x67a7895527fdf6b5 0x8ff803f03fffffff 0xf8ff803f03ffffff

def z1235 : W := mkw 0x04043229046284a8 0x004043229046284a 0x82d472690ce38cfe 0xe82d472690ce38cf

def z1236 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xf4880c1fc31f43fd 0x3f4880c1fc31f43f

def z1237 : W := mkw 0x4801808610945046 0x1480180861094504 0xb727818e30fc70cd 0xdb727818e30fc70c

def z1238 : W := mkw 0x80076aad80208088 0x180076aad8020808 0x7007fc0fc0e000c4 0x07007fc0fc0e000c

def z1239 : W := mkw 0x04043229046284a8 0x004043229046284a 0xc8d072690ce38cfe 0xec8d072690ce38cf

def z1240 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0f7803f03f00ff03 0xd0f7803f03f00ff0

def z1241 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x7f7ffd803fff3007 0xc7f7ffd803fff300

def z1242 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfda80d9ff31f73ff 0x7fda80d9ff31f73f

def z1243 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb727838e30fcb0c4 0x9b727838e30fcb0c

def z1244 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7f77fc003cff0007 0xc7f77fc003cff000

def z1245 : W := mkw 0x0c0522af0024d4ee 0x10c0522af0024d4e 0x8000038f0000f0f8 0x18000038f0000f0f

def z1246 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7027fc0030ff0004 0x07027fc0030ff000

def z1247 : W := mkw 0x627adc007fdb0111 0x4627adc007fdb011 0x7ffffc003fff0337 0xc7ffffc003fff033

def z1248 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x740ffc0003ff0005 0x0740ffc0003ff000

def z1249 : W := mkw 0x04043229046284a8 0x004043229046284a 0xd2d472690ce38cfc 0xad2d472690ce38cf

def z1250 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x267ffc003fff0007 0xc267ffc003fff000

def z1251 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xffffffffcf00ff0a 0x3ffffffffcf00ff0

def z1252 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7307fc0000ff0004 0xc7307fc0000ff000

def z1253 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdbdc72790fe38ffe 0xedbdc72790fe38ff

def z1254 : W := mkw 0x04043229046284a8 0x004043229046284a 0xd35472690ce38cfc 0xcd35472690ce38cf

def z1255 : W := mkw 0x980523ff8024face 0x3980523ff8024fac 0x808003ffc000ffc8 0x3808003ffc000ffc

def z1256 : W := mkw 0x0002480000000000 0x0000248000000000 0xfd0ffc1fc0000000 0x3fd0ffc1fc000000

def z1257 : W := mkw 0x100000002a002a00 0x0100000002a002a0 0x8ff003e03f00ff0b 0xf8ff003e03f00ff0

def z1258 : W := mkw 0x604094003fdb0000 0x0604094003fdb000 0x7f77f0003fff0007 0xc7f77f0003fff000

def z1259 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0x742ffd9033ff7305 0x1742ffd9033ff730

def z1260 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x82f003f03f00ff0b 0xf82f003f03f00ff0

def z1261 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb727839ff0fcf0cd 0xfb727839ff0fcf0c

def z1262 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x7d880c1fc31f03f7 0x67d880c1fc31f03f

def z1263 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0x78dffc7fcf000f02 0x278dffc7fcf000f0

def z1264 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x877803f03f00ff09 0xd877803f03f00ff0

def z1265 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xfff80fffff1fffff 0xffff80fffff1ffff

def z1266 : W := mkw 0xe07add50bfdb0000 0x6e07add50bfdb000 0x7f7ffc10ffff0007 0xc7f7ffc10ffff000

def z1267 : W := mkw 0x80076aad80000000 0x180076aad8000000 0x7817fc6fc0000000 0x27817fc6fc000000

def z1268 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x87f003e03f00ff0b 0xd87f003e03f00ff0

def z1269 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0xfd8ffc1003ff430f 0x7fd8ffc1003ff430

def z1270 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3727838030fcf0cd 0xc3727838030fcf0c

def z1271 : W := mkw 0x4005828c10b0908a 0x14005828c10b0908 0xb727838e30fcb005 0xdb727838e30fcb00

def z1272 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb72f8f9ef0fcf0cd 0xdb72f8f9ef0fcf0c

def z1273 : W := mkw 0x0c0522af0024d4ee 0x10c0522af0024d4e 0x8080026f00008cf8 0x28080026f00008cf

def z1274 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x7a3fffffc0000000 0x27a3fffffc000000

def z1275 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0xf727ff8030fff00d 0xdf727ff8030fff00

def z1276 : W := mkw 0x727add507fdb2b11 0x6727add507fdb2b1 0xfffffff1ffffff3f 0xffffffff1ffffff3

def z1277 : W := mkw 0x04043229046284a8 0x004043229046284a 0x5ad472690ce38cf6 0xa5ad472690ce38cf

def z1278 : W := mkw 0x4002c80010900000 0x04002c8001090000 0x7007fc0000fc0004 0x07007fc0000fc000

def z1279 : W := mkw 0x707adc003fdb2a00 0x4707adc003fdb2a0 0x7f7ffc003fffbc07 0xc7f7ffc003fffbc0

def z1280 : W := mkw 0x90076bfd80002a00 0x390076bfd80002a0 0xf087ffffc000ff08 0x3f087ffffc000ff0

def z1281 : W := mkw 0x04043229046284a8 0x004043229046284a 0x5b5472690ce38cf6 0xc5b5472690ce38cf

def z1282 : W := mkw 0x843f6bfd802084a8 0x7843f6bfd802084a 0xff3fffffc00000f0 0x3ff3fffffc00000f

def z1283 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xdff803f93f00ff0b 0xfdff803f93f00ff0

def z1284 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7ffc003cff0004 0x87f7ffc003cff000

def z1285 : W := mkw 0x407ad8003ed20000 0x4407ad8003ed2000 0x0277f0003cfc0005 0xc0277f0003cfc000

def z1286 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3ffffff0007001 0x3ff3ffffff000700

def z1287 : W := mkw 0x4e05a2af50b4d5ff 0x14e05a2af50b4d5f 0xb7a783fff0fcfffd 0xfb7a783fff0fcfff

def z1288 : W := mkw 0x4805828e10945046 0x14805828e1094504 0xb727838e30fc7005 0xdb727838e30fc700

def z1289 : W := mkw 0x0e0522af4024d5ff 0x10e0522af4024d5f 0x808003ffc000fff8 0x3808003ffc000fff

def z1290 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xfffffe703fff8f0f 0xefffffe703fff8f0

def z1291 : W := mkw 0x607adc0015db0000 0x4607adc0015db000 0x781ffc0000ff0004 0x0781ffc0000ff000

def z1292 : W := mkw 0x403ad80014d20000 0x4403ad80014d2000 0x7f7ffc003cff0007 0xc7f7ffc003cff000

def z1293 : W := mkw 0x003a480000000000 0x4003a48000000000 0x7f3ffc16c0000000 0x17f3ffc16c000000

def z1294 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xb7a7839e30fcf3cd 0xfb7a7839e30fcf3c

def z1295 : W := mkw 0x627adc007fdb0111 0x4627adc007fdb011 0x7f7ffc01ffff0037 0xc7f7ffc01ffff003

def z1296 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0x267ffff6ff00ff01 0x9267ffff6ff00ff0

def z1297 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xfffffc003fff000f 0xefffffc003fff000

def z1298 : W := mkw 0x407ad8003ed20000 0x4407ad8003ed2000 0x7f77f0003cff0007 0xc7f77f0003cff000

def z1299 : W := mkw 0x803b49d480000000 0x7803b49d48000000 0x6c3bfd96c0000000 0x16c3bfd96c000000

def z1300 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x767ffc003fff0005 0x8767ffc003fff000

def z1301 : W := mkw 0x6a4094027fdf4155 0x06a4094027fdf415 0x004000003fff4307 0xc004000003fff430

def z1302 : W := mkw 0x4000900014d20000 0x04000900014d2000 0x7b57f0000cff0006 0xc7b57f0000cff000

def z1303 : W := mkw 0x903b49d4aa002a00 0x7903b49d4aa002a0 0x7f7ffd96ff007303 0xd7f7ffd96ff00730

def z1304 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0xfff783ef3cfffcff 0xffff783ef3cfffcf

def z1305 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdbd472690ce30cf6 0x2dbd472690ce30cf

def z1306 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xfff80ff03f00ff0b 0xffff80ff03f00ff0

def z1307 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xfd2ffd9fc0000000 0x3fd2ffd9fc000000

def z1308 : W := mkw 0x4a05828e50b4d1df 0x14a05828e50b4d1d 0xffaf8f9ff0fcf3fd 0xfffaf8f9ff0fcf3f

def z1309 : W := mkw 0x4805828e10b4d0ce 0x14805828e10b4d0c 0x3727838630fcf005 0xd3727838630fcf00

def z1310 : W := mkw 0x04043229046284a8 0x004043229046284a 0xdfdc72690fe38cff 0xedfdc72690fe38cf

def z1311 : W := mkw 0x843f6bfd80000420 0x7843f6bfd8000042 0xffbfffffc0000c30 0x3ffbfffffc0000c3

def z1312 : W := mkw 0x903f6bfdaa002a00 0x7903f6bfdaa002a0 0xffffffffcf004f0b 0x7ffffffffcf004f0

def z1313 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xfffffff03fff0f07 0xffffffff03fff0f0

def z1314 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7857fc000cff0006 0x07857fc000cff000

def z1315 : W := mkw 0x707add503fdb2a00 0x6707add503fdb2a0 0xff7fffe03ffffc0f 0xdff7fffe03ffffc0

def z1316 : W := mkw 0x803f6bfd8020908a 0x7803f6bfd8020908 0xff3fffffc000b000 0x3ff3fffffc000b00

def z1317 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x7f3ffc7fc0000000 0x27f3ffc7fc000000

def z1318 : W := mkw 0x4a05828e50b4d1df 0x14a05828e50b4d1d 0xb727839ef0fcf3cd 0xdb727839ef0fcf3c

def z1319 : W := mkw 0x6a4094027fffd1df 0x06a4094027fffd1d 0x00c000003ffff3ff 0xc00c000003ffff3f

def z1320 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0x7f7fff803fffb007 0xc7f7fff803fffb00

def z1321 : W := mkw 0x80076bfd80000000 0x380076bfd8000000 0xfd0fffffc0000000 0x3fd0fffffc000000

def z1322 : W := mkw 0x6242dc0055db0111 0x06242dc0055db011 0x788ffc11c3ff0336 0x2788ffc11c3ff033

def z1323 : W := mkw 0x800368a580000000 0x1800368a58000000 0x6003fc07c0000000 0x06003fc07c000000

def z1324 : W := mkw 0x4801808610945046 0x1480180861094504 0x2423818630fc7005 0xd2423818630fc700

def z1325 : W := mkw 0x607adc003fdb0000 0x4607adc003fdb000 0xfffffc1fffff00ff 0xffffffc1fffff00f

def z1326 : W := mkw 0x403890003ed20000 0x4403890003ed2000 0x7f7ff0003fff0007 0xc7f7ff0003fff000

def z1327 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x700ffc1fc0000000 0x0700ffc1fc000000

def z1328 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0x7027fd8fc0000000 0x07027fd8fc000000

def z1329 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x70080c1fc31f03f4 0x070080c1fc31f03f

def z1330 : W := mkw 0x843f6bfd802084a8 0x7843f6bfd802084a 0xff3fffffc0008c00 0x3ff3fffffc0008c0

def z1331 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0x0ef803f03f00ff03 0xb0ef803f03f00ff0

def z1332 : W := mkw 0x6042dc0015db0000 0x06042dc0015db000 0x7427fc0030ff0005 0x07427fc0030ff000

def z1333 : W := mkw 0x6e4094027fffc5fd 0x06e4094027fffc5f 0x00c000003fffcfff 0xc00c000003fffcff

def z1334 : W := mkw 0x803f6bfdaa000000 0x7803f6bfdaa00000 0xff7ffffffc000000 0xbff7ffffffc00000

def z1335 : W := mkw 0x80076aad80000000 0x180076aad8000000 0xf507fc0fc0000000 0x1f507fc0fc000000

def z1336 : W := mkw 0x100001502a002a00 0x2100001502a002a0 0x8bd003f03f00ff0b 0xf8bd003f03f00ff0

def z1337 : W := mkw 0x607adc0015db0000 0x4607adc0015db000 0x7f7ffc000cff0006 0xc7f7ffc000cff000

def z1338 : W := mkw 0x903f6bfd80002a00 0x7903f6bfd80002a0 0xffffffffcc00ff0a 0xfffffffffcc00ff0

def z1339 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0x78880c1fc31f43ff 0x678880c1fc31f43f

def z1340 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xf72fff9fc0000000 0x1f72fff9fc000000

def z1341 : W := mkw 0x4801808610b4d0ce 0x14801808610b4d0c 0x3727818630fcf0cd 0xd3727818630fcf0c

def z1342 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xffa80f9fc31f43ff 0x7ffa80f9fc31f43f

def z1343 : W := mkw 0x103801502a002a00 0x6103801502a002a0 0xdffc73f03f00ff0b 0xfdffc73f03f00ff0

def z1344 : W := mkw 0x0400302104420420 0x0040030210442042 0xdbd470690ce30cfe 0xedbd470690ce30cf

def z1345 : W := mkw 0x803f6bfd80000000 0x7803f6bfd8000000 0xff3fffffc01c0005 0x7ff3fffffc01c000

def z1346 : W := mkw 0x2a000402410d4155 0x02a000402410d415 0xc8880c1fc31f43ff 0x7c8880c1fc31f43f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z8,z5,z9]),(0,[z1,z10,z2,z3,z8,z11,z6]),(0,[z1,z2,z12,z3,z8,z5,z6]),(0,[z1,z13,z2,z3,z8,z5,z6]),(0,[z1,z14,z2,z3,z8,z5,z6]),(0,[z1,z2,z15,z3,z8,z5,z16]),(0,[z1,z2,z15,z3,z8,z17,z5]),(0,[z1,z18,z2,z3,z8,z5,z6]),(0,[z1,z19,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z20,z6]),(0,[z7,z2,z3,z21,z8,z5,z6]),(0,[z22,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z23,z3,z8,z5,z6]),(0,[z1,z24,z2,z3,z8,z5,z6]),(0,[z25,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z26,z6]),(0,[z1,z27,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z28,z8,z5,z6]),(0,[z1,z2,z29,z3,z8,z5,z6]),(0,[z30,z1,z2,z3,z8,z5,z31]),(1,[z32,z2,z3,z33,z5,z6]),(0,[z34,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z35,z3,z36,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z37])],[(0,[z38,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z39,z5,z6]),(0,[z40,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z41,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z42,z43]),(0,[z44,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z45])],[(0,[z1,z2,z46,z3,z8,z11,z6]),(0,[z47,z1,z2,z3,z8,z11,z6]),(0,[z7,z1,z2,z3,z8,z48,z6]),(1,[z1,z2,z3,z49,z5,z6]),(0,[z1,z2,z3,z8,z48,z6,z37]),(0,[z1,z2,z3,z50,z8,z5,z6]),(0,[z1,z2,z35,z3,z8,z51,z6]),(1,[z1,z2,z3,z8,z5,z52]),(0,[z53,z1,z2,z3,z54,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z55])],[(0,[z1,z2,z56,z3,z8,z5,z42]),(0,[z1,z2,z57,z3,z8,z5,z6]),(0,[z1,z2,z15,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z58,z6])],[(0,[z59,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z33,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z61,z42])],[(0,[z62,z1,z2,z3,z8,z5,z6]),(0,[z63,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z64]),(0,[z1,z2,z3,z8,z5,z65,z6]),(0,[z1,z2,z3,z8,z66,z5,z6])]],
   [[(0,[z67,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z68,z6]),(0,[z1,z69,z2,z3,z8,z5,z6]),(0,[z53,z70,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z16,z6])],[(0,[z71,z2,z3,z21,z8,z5,z6]),(0,[z1,z2,z3,z8,z72,z48,z6]),(0,[z1,z2,z3,z73,z5,z48,z6]),(0,[z74,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z75,z6]),(0,[z1,z2,z76,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z6,z77])],[(0,[z30,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z68,z60]),(0,[z78,z1,z2,z3,z8,z5,z60])],[(0,[z1,z2,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z79]),(1,[z1,z2,z3,z8,z48,z42]),(0,[z1,z2,z3,z80,z8,z48,z6]),(0,[z81,z1,z2,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z5,z82,z6])],[(0,[z1,z2,z3,z8,z5,z6,z83]),(0,[z1,z2,z3,z8,z84,z5,z6])],[(0,[z85,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z86]),(0,[z1,z2,z3,z8,z5,z87,z6])],[(0,[z1,z2,z3,z8,z5,z6,z88]),(0,[z1,z2,z3,z89,z8,z5,z42]),(0,[z1,z2,z3,z8,z5,z90,z6])],[(0,[z91,z1,z2,z3,z8,z5,z60]),(1,[z1,z2,z3,z92,z5,z6]),(0,[z93,z94,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z48,z95,z6])]],
   [[(0,[z1,z2,z96,z3,z8,z11,z6]),(0,[z1,z97,z2,z3,z8,z5,z6]),(0,[z1,z98,z2,z3,z8,z99,z6]),(0,[z1,z2,z3,z8,z5,z42,z42]),(0,[z1,z2,z3,z100,z8,z5,z6]),(0,[z101,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z102])],[(0,[z71,z1,z2,z3,z8,z5,z88]),(1,[z1,z3,z103,z8,z5,z60]),(0,[z1,z2,z3,z104,z8,z48,z6]),(0,[z1,z2,z3,z105,z8,z5,z6]),(0,[z106,z1,z2,z3,z8,z5,z6])],[(0,[z32,z1,z2,z3,z8,z11,z6]),(0,[z1,z2,z3,z33,z8,z11,z6]),(0,[z1,z2,z3,z33,z5,z107,z6]),(0,[z1,z2,z3,z8,z5,z95,z9]),(1,[z1,z2,z3,z8,z5,z108]),(0,[z1,z2,z3,z8,z5,z72,z6]),(0,[z1,z109,z2,z3,z8,z5,z42]),(0,[z1,z2,z110,z3,z8,z5,z42]),(0,[z1,z2,z3,z8,z111,z5,z42]),(0,[z112,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z113,z6]),(1,[z1,z114,z3,z8,z5,z6]),(0,[z115,z1,z2,z3,z8,z5,z6]),(0,[z116,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z117,z3,z8,z5,z6]),(0,[z47,z1,z2,z3,z8,z5,z118]),(0,[z119,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z35,z3,z8,z48,z6])],[(0,[z1,z2,z3,z120,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z121,z6]),(0,[z1,z2,z3,z122,z8,z5,z42]),(0,[z123,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z124,z6,z125])],[(0,[z1,z126,z2,z3,z8,z5,z20]),(0,[z127,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z128,z8,z5,z6]),(0,[z1,z2,z56,z3,z8,z48,z6]),(0,[z1,z2,z3,z129,z8,z5,z6]),(0,[z1,z2,z3,z130,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z107,z42]),(0,[z1,z2,z3,z8,z5,z131,z6])],[(1,[z1,z2,z3,z73,z48,z6]),(0,[z1,z2,z3,z8,z5,z6,z132]),(0,[z1,z2,z3,z8,z5,z6,z133]),(0,[z1,z2,z3,z134,z8,z6,z45]),(0,[z1,z2,z3,z8,z5,z135,z6]),(0,[z136,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z137]),(0,[z1,z2,z35,z103,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z138,z6]),(0,[z1,z2,z3,z8,z5,z139,z6]),(0,[z1,z2,z3,z89,z8,z5,z95])]],
   [[(0,[z7,z1,z2,z3,z8,z5,z6]),(0,[z85,z1,z2,z3,z80,z5,z6]),(0,[z1,z2,z140,z3,z8,z48,z6]),(0,[z141,z1,z2,z3,z8,z5,z6]),(0,[z81,z1,z2,z3,z5,z6,z45]),(0,[z1,z2,z3,z89,z8,z5,z45])],[(0,[z32,z142,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z31,z6]),(0,[z25,z1,z2,z3,z8,z5,z143]),(0,[z144,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z145]),(1,[z1,z2,z3,z8,z146,z6]),(0,[z85,z1,z2,z3,z8,z147,z6]),(0,[z1,z2,z3,z8,z48,z48,z6]),(0,[z1,z2,z3,z8,z5,z42,z37])],[(0,[z148,z1,z2,z3,z8,z5,z6]),(0,[z1,z149,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z150,z8,z5,z6]),(0,[z1,z151,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z8,z5,z152,z6]),(0,[z1,z2,z3,z8,z5,z6,z153]),(0,[z1,z2,z3,z154,z8,z5,z6])],[(1,[z1,z2,z3,z8,z155,z6]),(0,[z1,z2,z156,z3,z8,z5,z6]),(0,[z91,z1,z2,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z5,z157,z6]),(0,[z1,z2,z3,z158,z8,z159,z6]),(0,[z1,z2,z3,z160,z8,z5,z6]),(0,[z1,z2,z3,z8,z135,z6,z125])],[(0,[z161,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z162]),(0,[z1,z2,z3,z163,z8,z5,z6])],[(0,[z164,z1,z2,z3,z8,z5,z60])],[(0,[z1,z2,z3,z8,z11,z9,z6]),(0,[z165,z1,z2,z3,z8,z5,z6]),(0,[z1,z166,z2,z3,z8,z5,z6])],[(0,[z93,z1,z2,z3,z49,z5,z6]),(0,[z1,z98,z2,z3,z8,z5,z167]),(1,[z1,z2,z3,z8,z5,z42]),(0,[z1,z2,z168,z3,z8,z5,z60]),(0,[z1,z14,z2,z3,z8,z5,z42]),(0,[z1,z109,z2,z3,z169,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z170]),(0,[z1,z2,z3,z80,z8,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z171,z6]),(0,[z1,z126,z2,z3,z8,z172,z6]),(0,[z71,z1,z2,z3,z8,z5,z6]),(0,[z173,z1,z2,z21,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z9,z60]),(0,[z1,z174,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z175,z6])],[(0,[z1,z2,z3,z8,z5,z176,z6]),(0,[z177,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z178])],[(0,[z30,z1,z2,z3,z8,z5,z179]),(0,[z1,z2,z3,z8,z180,z5,z6]),(0,[z1,z2,z3,z8,z48,z171,z6]),(0,[z1,z2,z3,z8,z5,z6,z181])],[(0,[z93,z1,z2,z3,z8,z11,z6]),(0,[z1,z2,z182,z3,z80,z8,z6]),(1,[z1,z19,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z17,z135])],[(1,[z1,z2,z3,z8,z5,z183]),(0,[z142,z1,z46,z3,z8,z5,z6]),(0,[z71,z173,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z89,z33,z5,z6]),(0,[z1,z94,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z184,z8,z5,z6]),(0,[z185,z1,z2,z3,z8,z11,z6])],[(0,[z1,z2,z3,z8,z186,z5,z6]),(0,[z187,z1,z2,z3,z8,z5,z6]),(0,[z85,z1,z2,z3,z104,z5,z6]),(0,[z1,z188,z2,z3,z8,z5,z6])],[(0,[z1,z189,z2,z3,z8,z5,z6]),(0,[z190,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z6,z191]),(0,[z1,z192,z2,z3,z8,z5,z6]),(0,[z193,z1,z194,z2,z3,z8,z6])],[(0,[z119,z1,z2,z3,z8,z5,z6]),(0,[z1,z10,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z195,z6]),(0,[z1,z2,z35,z3,z8,z5,z6]),(0,[z1,z2,z35,z36,z8,z5,z6]),(0,[z1,z2,z196,z3,z8,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z8,z5,z197]),(0,[z1,z2,z3,z103,z8,z11,z6]),(0,[z1,z2,z3,z8,z5,z6,z198]),(0,[z1,z2,z3,z8,z5,z6,z199]),(0,[z1,z200,z2,z3,z8,z11,z6]),(0,[z1,z200,z2,z3,z5,z107,z6])],[(0,[z30,z1,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z158,z8,z68,z6]),(0,[z1,z2,z56,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z201]),(0,[z1,z2,z202,z3,z8,z5,z6]),(0,[z164,z1,z2,z3,z8,z11,z6]),(0,[z1,z14,z3,z8,z5,z42,z6])],[(0,[z1,z203,z2,z3,z8,z5,z6]),(0,[z1,z2,z204,z3,z8,z5,z6]),(1,[z1,z2,z3,z205,z5,z6]),(0,[z206,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z207,z3,z8,z5,z6]),(1,[z1,z2,z3,z73,z5,z6]),(0,[z1,z2,z2,z3,z8,z5,z42])],[(0,[z0,z1,z2,z3,z208,z5,z6]),(0,[z1,z2,z46,z3,z8,z48,z6]),(0,[z1,z10,z2,z103,z8,z5,z6]),(0,[z209,z1,z2,z3,z8,z5,z6]),(0,[z85,z1,z2,z3,z8,z5,z210]),(0,[z1,z2,z211,z3,z8,z5,z6]),(0,[z1,z2,z3,z212,z8,z5,z6])],[(0,[z0,z1,z2,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z213,z5,z6]),(0,[z193,z1,z2,z3,z8,z5,z9]),(1,[z1,z10,z3,z8,z5,z60]),(0,[z85,z1,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z36,z8,z5,z60]),(0,[z1,z2,z140,z3,z8,z5,z6]),(1,[z1,z2,z3,z169,z5,z6]),(0,[z1,z2,z214,z3,z8,z5,z6])],[(0,[z215,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z216,z6]),(0,[z2,z3,z33,z8,z217,z5,z6]),(0,[z1,z2,z218,z3,z8,z11,z6]),(0,[z1,z219,z2,z3,z8,z5,z6]),(0,[z1,z2,z182,z3,z36,z5,z6]),(0,[z1,z220,z2,z3,z8,z5,z6]),(0,[z1,z221,z2,z3,z8,z5,z6])],[(0,[z1,z2,z21,z103,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z222]),(0,[z1,z2,z3,z8,z5,z118,z60]),(0,[z223,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z182,z3,z8,z5,z42])],[(0,[z1,z224,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z6,z225]),(0,[z1,z2,z3,z8,z5,z42,z16]),(0,[z1,z2,z3,z226,z8,z5,z6]),(0,[z193,z1,z2,z3,z8,z6,z125])]],
   [[(0,[z1,z1,z2,z3,z8,z5,z6]),(0,[z1,z151,z2,z3,z8,z5,z227]),(0,[z228,z1,z2,z3,z8,z5,z42]),(0,[z1,z229,z2,z3,z8,z5,z6]),(0,[z1,z230,z2,z3,z8,z5,z6])],[(0,[z142,z1,z126,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z172,z6]),(0,[z1,z2,z3,z8,z8,z5,z6]),(0,[z1,z2,z3,z231,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z232,z6])],[(0,[z81,z1,z2,z3,z8,z48,z6]),(1,[z1,z2,z3,z8,z233,z6]),(0,[z234,z1,z2,z3,z8,z5,z6]),(0,[z235,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z217,z5,z60]),(0,[z25,z1,z2,z3,z236,z5,z6]),(0,[z1,z2,z3,z236,z8,z5,z6]),(0,[z1,z237,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z6,z37]),(0,[z1,z2,z3,z8,z5,z238,z6])],[(0,[z1,z2,z3,z8,z5,z239,z6]),(1,[z1,z2,z3,z8,z5,z88]),(0,[z1,z2,z3,z8,z5,z6,z240]),(0,[z1,z2,z3,z8,z5,z241,z6]),(0,[z1,z2,z3,z8,z5,z42,z6])],[(0,[z71,z1,z2,z3,z242,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z143])],[(0,[z243,z1,z2,z3,z8,z5,z6]),(0,[z71,z1,z224,z3,z8,z5,z6]),(1,[z1,z98,z3,z104,z5,z6]),(0,[z1,z2,z110,z3,z8,z5,z6])],[(0,[z1,z2,z96,z3,z8,z48,z6]),(1,[z1,z244,z2,z3,z8,z6]),(0,[z91,z1,z2,z3,z8,z159,z6]),(1,[z91,z2,z3,z8,z68,z6])]],
   [[(0,[z1,z2,z3,z21,z8,z5,z42]),(0,[z1,z2,z3,z89,z217,z5,z6]),(0,[z1,z2,z3,z8,z5,z245,z6]),(0,[z1,z2,z3,z8,z11,z5,z42]),(0,[z1,z2,z246,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z247]),(0,[z1,z2,z248,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z249])],[(0,[z32,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z6,z250]),(1,[z1,z2,z3,z8,z5,z138]),(0,[z1,z2,z3,z8,z251,z5,z42]),(0,[z1,z2,z3,z8,z11,z16,z6]),(0,[z59,z1,z2,z3,z8,z5,z60]),(1,[z1,z2,z3,z8,z252,z6]),(0,[z1,z2,z3,z8,z5,z253,z6])],[(0,[z1,z2,z254,z3,z8,z5,z6]),(1,[z1,z2,z140,z8,z124,z6]),(0,[z1,z2,z255,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z256])],[(1,[z1,z2,z3,z8,z5,z257]),(0,[z1,z2,z96,z103,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z31]),(1,[z1,z2,z3,z8,z11,z60]),(0,[z1,z258,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z259,z5,z6]),(0,[z1,z2,z3,z8,z68,z124,z6]),(0,[z1,z2,z3,z8,z260,z11,z6]),(0,[z164,z1,z2,z3,z8,z261,z6]),(0,[z262,z1,z2,z3,z8,z5,z6]),(0,[z1,z263,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z11,z159,z6]),(0,[z264,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z265]),(0,[z193,z1,z2,z3,z8,z5,z125])],[(0,[z266,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z20]),(0,[z1,z2,z182,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z267,z6]),(0,[z1,z268,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z95,z6]),(0,[z1,z2,z3,z80,z8,z5,z42]),(0,[z1,z200,z2,z3,z36,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z269])],[(0,[z1,z2,z46,z3,z8,z5,z6]),(0,[z270,z1,z2,z3,z8,z5,z6]),(0,[z30,z1,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z271]),(0,[z1,z14,z151,z3,z8,z5,z6]),(0,[z272,z1,z2,z3,z8,z11,z6])]],
   [[(0,[z273,z1,z2,z3,z8,z5,z6]),(0,[z1,z151,z3,z8,z5,z6,z60]),(0,[z1,z274,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z275,z5,z6]),(0,[z1,z2,z3,z8,z5,z60,z37]),(0,[z1,z2,z3,z8,z5,z95,z60]),(0,[z1,z2,z3,z8,z5,z52,z124])],[(0,[z276,z1,z2,z3,z8,z5,z6]),(0,[z85,z1,z2,z182,z3,z5,z6])],[(0,[z1,z277,z2,z3,z8,z5,z6]),(0,[z278,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z80,z5,z279,z6])],[(1,[z1,z2,z3,z8,z5,z6]),(0,[z25,z1,z194,z2,z3,z8,z6]),(0,[z1,z2,z3,z280,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z42,z281]),(0,[z1,z282,z2,z3,z8,z5,z6])],[(0,[z71,z1,z2,z3,z8,z283,z6]),(0,[z1,z2,z3,z104,z8,z5,z42]),(0,[z1,z2,z3,z8,z5,z124,z6]),(0,[z1,z2,z284,z3,z8,z5,z6])],[(0,[z1,z2,z3,z285,z8,z5,z6]),(0,[z91,z1,z2,z3,z8,z68,z6]),(0,[z286,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z227,z6]),(0,[z287,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z36,z8,z5,z107,z6]),(0,[z1,z2,z288,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z289])],[(0,[z173,z142,z2,z3,z8,z5,z6]),(0,[z85,z1,z2,z3,z8,z290,z6]),(0,[z85,z1,z2,z3,z8,z5,z138]),(0,[z291,z1,z2,z3,z8,z48,z6]),(0,[z119,z1,z2,z3,z8,z5,z42]),(0,[z1,z2,z35,z3,z8,z5,z42]),(0,[z292,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z17,z5,z42]),(0,[z81,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z293,z8,z5,z6]),(1,[z1,z151,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z11,z135,z6]),(0,[z1,z2,z3,z8,z5,z294,z6])]],
   [[(0,[z1,z2,z3,z21,z8,z48,z6]),(0,[z1,z2,z3,z295,z8,z5,z6]),(0,[z1,z296,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z297,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z298,z6]),(0,[z1,z2,z3,z8,z11,z48,z6]),(0,[z1,z2,z3,z8,z48,z6,z45])],[(0,[z0,z1,z2,z299,z8,z5,z6]),(0,[z1,z2,z300,z3,z8,z5,z6]),(0,[z1,z2,z301,z3,z8,z5,z6]),(0,[z1,z2,z302,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z251,z48,z6]),(0,[z1,z98,z2,z3,z8,z11,z6]),(0,[z1,z194,z2,z3,z8,z11,z6]),(0,[z1,z109,z2,z3,z158,z8,z6]),(0,[z53,z1,z303,z3,z8,z5,z6]),(0,[z1,z304,z2,z3,z8,z5,z6])],[(0,[z93,z1,z2,z3,z8,z48,z6]),(0,[z305,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z48,z60]),(0,[z1,z2,z306,z3,z8,z5,z6])],[(0,[z91,z25,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z307,z5,z6]),(0,[z1,z2,z3,z8,z5,z308,z6]),(0,[z53,z1,z2,z3,z8,z11,z6]),(0,[z1,z2,z140,z3,z8,z5,z42]),(0,[z309,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z310,z8,z5,z6]),(0,[z2,z3,z21,z8,z5,z6,z118]),(0,[z1,z2,z3,z311,z8,z217,z6]),(0,[z1,z2,z3,z311,z8,z5,z6]),(0,[z1,z151,z3,z8,z11,z5,z6]),(0,[z1,z2,z3,z8,z5,z312,z6]),(0,[z1,z2,z313,z3,z8,z5,z6])],[(0,[z0,z1,z2,z3,z8,z314,z6]),(0,[z1,z126,z2,z3,z8,z5,z60]),(0,[z32,z1,z2,z3,z8,z5,z6]),(0,[z93,z1,z2,z3,z8,z315,z6]),(0,[z1,z10,z2,z3,z8,z5,z108]),(0,[z1,z2,z3,z8,z48,z16,z6]),(0,[z1,z2,z3,z8,z5,z316,z6]),(0,[z1,z2,z3,z80,z8,z135,z6]),(0,[z1,z317,z2,z3,z8,z5,z6])],[(0,[z47,z1,z2,z3,z92,z5,z6]),(0,[z93,z1,z2,z103,z8,z5,z6]),(0,[z1,z2,z3,z8,z318,z5,z6]),(0,[z1,z319,z2,z3,z8,z5,z6]),(0,[z1,z320,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z321,z6]),(0,[z1,z322,z2,z3,z8,z5,z6])],[(0,[z323,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z324,z8,z5,z6]),(0,[z1,z2,z3,z103,z8,z48,z6]),(1,[z1,z2,z3,z8,z147,z6]),(0,[z1,z200,z2,z3,z8,z48,z6]),(0,[z325,z1,z2,z3,z8,z5,z6]),(0,[z1,z109,z2,z3,z8,z124,z6]),(1,[z263,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z183,z6]),(0,[z1,z2,z326,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z327]),(0,[z1,z2,z3,z8,z5,z6,z60]),(0,[z70,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z328,z8,z5,z6]),(0,[z1,z2,z3,z251,z5,z107,z6]),(0,[z1,z329,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z330,z5,z6]),(0,[z53,z193,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z17,z5,z135])],[(0,[z1,z2,z3,z73,z8,z48,z6]),(0,[z331,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z182,z3,z8,z5,z6]),(0,[z81,z263,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z332])],[(0,[z228,z1,z2,z3,z8,z5,z6]),(0,[z1,z333,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z334,z5,z6]),(0,[z1,z2,z3,z80,z33,z5,z6]),(0,[z1,z10,z2,z3,z8,z146,z6]),(0,[z335,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z336,z6]),(1,[z1,z2,z15,z8,z5,z16]),(0,[z1,z2,z3,z337,z8,z5,z6])],[(0,[z338,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z339,z5,z6]),(0,[z53,z1,z114,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z17,z135,z6])],[(0,[z173,z1,z2,z3,z8,z5,z42]),(0,[z1,z2,z340,z3,z8,z5,z6]),(0,[z341,z1,z2,z3,z8,z5,z6]),(0,[z305,z1,z151,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z17,z48,z6]),(0,[z1,z2,z3,z342,z8,z5,z6])],[(0,[z1,z126,z2,z3,z8,z343,z6]),(0,[z1,z2,z344,z3,z8,z5,z6]),(0,[z1,z2,z3,z345,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z346,z6]),(0,[z1,z2,z3,z347,z8,z11,z6]),(1,[z1,z2,z3,z8,z348,z6]),(0,[z1,z14,z2,z3,z8,z348,z6]),(0,[z1,z2,z15,z8,z5,z16,z6])]],
   [[(1,[z1,z2,z3,z242,z5,z6]),(0,[z349,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z195,z6]),(0,[z350,z1,z2,z3,z8,z5,z60]),(0,[z351,z1,z2,z3,z8,z5,z6])],[(1,[z1,z224,z3,z8,z5,z6]),(1,[z47,z2,z3,z8,z5,z118]),(0,[z1,z2,z3,z158,z8,z5,z42])],[(1,[z1,z2,z352,z8,z5,z6]),(0,[z1,z353,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z354,z8,z5,z6]),(0,[z25,z2,z3,z8,z159,z5,z6]),(1,[z1,z2,z3,z8,z5,z240]),(0,[z1,z10,z2,z3,z8,z5,z42]),(0,[z193,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z355,z3,z8,z5,z6]),(0,[z53,z1,z2,z3,z356,z5,z6]),(0,[z357,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z358,z6]),(1,[z1,z2,z3,z8,z5,z179]),(0,[z1,z2,z3,z8,z5,z359,z6]),(0,[z1,z2,z3,z8,z205,z5,z6]),(1,[z1,z2,z3,z8,z5,z143]),(0,[z1,z2,z3,z8,z5,z95,z118]),(0,[z1,z2,z3,z8,z5,z6,z360]),(0,[z1,z2,z3,z8,z48,z135,z6]),(0,[z361,z1,z2,z3,z8,z5,z6]),(0,[z362,z1,z2,z3,z8,z5,z6]),(0,[z1,z363,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z134,z8,z6])],[(0,[z32,z2,z46,z3,z8,z5,z6]),(0,[z1,z2,z3,z21,z8,z5,z6]),(0,[z1,z364,z2,z3,z8,z5,z6]),(0,[z365,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z5,z6]),(0,[z1,z2,z3,z8,z5,z42,z95]),(0,[z1,z2,z3,z8,z5,z366,z6])],[(0,[z1,z2,z3,z8,z5,z367,z6]),(0,[z1,z368,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z251,z5,z6]),(0,[z1,z2,z3,z8,z5,z267,z42]),(0,[z1,z2,z3,z8,z5,z42,z45]),(0,[z1,z2,z3,z8,z369,z5,z6])],[(0,[z1,z2,z46,z3,z8,z5,z42]),(0,[z71,z1,z300,z3,z8,z5,z6]),(0,[z1,z2,z3,z370,z8,z5,z6]),(1,[z1,z2,z3,z120,z5,z6]),(0,[z47,z1,z2,z3,z8,z5,z42]),(0,[z93,z1,z2,z3,z8,z5,z6]),(0,[z85,z371,z2,z3,z8,z5,z6]),(1,[z85,z1,z3,z251,z5,z6]),(0,[z1,z2,z3,z372,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z373]),(0,[z7,z173,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z250]),(0,[z85,z1,z3,z8,z251,z5,z6]),(0,[z185,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z233,z5,z6]),(0,[z1,z2,z3,z374,z8,z5,z60])]],
   [[(0,[z1,z2,z3,z375,z8,z5,z6]),(0,[z7,z1,z2,z3,z8,z5,z9]),(0,[z85,z1,z2,z376,z8,z5,z6]),(1,[z1,z2,z35,z36,z5,z6])],[(0,[z71,z1,z2,z96,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z210]),(0,[z1,z2,z3,z8,z5,z377,z6]),(1,[z1,z109,z2,z158,z8,z6]),(0,[z1,z2,z378,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z379,z6])],[(0,[z7,z2,z3,z8,z217,z5,z6]),(0,[z1,z2,z3,z33,z5,z6,z45]),(0,[z1,z2,z3,z8,z5,z380,z6]),(0,[z1,z2,z3,z8,z5,z6,z381])],[(0,[z1,z2,z3,z8,z5,z6,z382]),(0,[z1,z2,z3,z383,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z124,z42]),(0,[z1,z200,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z384])],[(0,[z385,z1,z2,z3,z8,z5,z6]),(0,[z1,z386,z2,z3,z8,z5,z6]),(0,[z1,z98,z2,z3,z8,z387,z6])],[(0,[z1,z2,z3,z8,z388,z5,z6]),(0,[z1,z2,z389,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z390,z6]),(0,[z1,z391,z2,z3,z8,z48,z6]),(0,[z392,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z89,z8,z5,z60]),(0,[z292,z1,z2,z3,z8,z5,z42]),(0,[z81,z1,z2,z3,z8,z5,z42]),(1,[z193,z1,z2,z3,z8,z125])],[(0,[z142,z1,z2,z3,z8,z5,z60]),(0,[z173,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z393,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z327,z6]),(0,[z193,z1,z2,z3,z8,z11,z6])],[(1,[z1,z2,z3,z8,z283,z6]),(1,[z394,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z395,z5,z6]),(0,[z396,z1,z2,z3,z8,z5,z124]),(1,[z397,z2,z3,z8,z5,z6])]],
   [[(0,[z398,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z103,z8,z5,z107,z6]),(0,[z1,z2,z3,z104,z8,z5,z6])],[(0,[z1,z2,z56,z8,z5,z107,z6]),(0,[z1,z2,z3,z158,z8,z48,z6]),(0,[z1,z109,z2,z3,z8,z5,z60])],[(0,[z399,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z96,z3,z8,z5,z42]),(0,[z91,z1,z2,z3,z80,z8,z6]),(0,[z1,z2,z3,z8,z11,z107,z6]),(0,[z1,z2,z3,z8,z5,z400,z6]),(0,[z1,z2,z3,z8,z17,z5,z6])],[(0,[z1,z2,z3,z8,z5,z401,z6]),(0,[z1,z2,z3,z402,z8,z5,z6]),(1,[z93,z1,z103,z8,z5,z6]),(0,[z53,z1,z2,z3,z8,z5,z37])],[(0,[z126,z2,z46,z3,z8,z5,z6]),(0,[z403,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z404,z6]),(0,[z32,z1,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z33,z8,z5,z42]),(0,[z1,z2,z3,z8,z405,z5,z6]),(0,[z406,z1,z2,z3,z8,z5,z6]),(0,[z85,z1,z2,z129,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z107,z60]),(0,[z1,z2,z3,z407,z8,z5,z6])],[(0,[z1,z2,z3,z8,z48,z6,z199])],[(0,[z1,z2,z3,z8,z408,z5,z6]),(0,[z47,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z409,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z410,z6]),(0,[z164,z1,z14,z3,z8,z5,z6]),(1,[z164,z1,z3,z8,z5,z60]),(0,[z81,z1,z2,z3,z8,z5,z45])]],
   [[(0,[z1,z2,z3,z411,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z412,z6]),(0,[z1,z98,z2,z3,z8,z48,z6]),(0,[z1,z194,z2,z3,z8,z48,z6])],[(0,[z1,z151,z2,z3,z8,z5,z60]),(0,[z413,z1,z2,z3,z8,z5,z6])],[(0,[z142,z1,z2,z3,z8,z11,z6]),(0,[z1,z126,z3,z103,z8,z5,z6]),(0,[z53,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z124,z48,z6]),(0,[z193,z1,z2,z3,z80,z8,z6]),(0,[z1,z2,z3,z414,z8,z5,z6])],[(0,[z1,z2,z3,z415,z8,z5,z6]),(0,[z1,z14,z10,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z416]),(0,[z1,z2,z3,z8,z5,z279,z42]),(0,[z1,z2,z417,z3,z8,z5,z6])],[(0,[z1,z2,z418,z3,z8,z5,z6])],[(0,[z91,z1,z2,z3,z8,z5,z42]),(1,[z1,z2,z3,z236,z5,z6]),(0,[z1,z2,z3,z8,z159,z48,z6]),(0,[z1,z2,z3,z8,z5,z6,z419]),(0,[z193,z1,z2,z3,z8,z5,z118]),(0,[z1,z2,z3,z8,z5,z6,z167]),(0,[z1,z2,z3,z8,z5,z52,z6]),(0,[z1,z2,z3,z80,z158,z8,z6]),(0,[z1,z2,z182,z3,z5,z279,z6])],[(0,[z0,z142,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z311,z8,z6]),(0,[z1,z420,z2,z3,z8,z5,z6]),(0,[z1,z14,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z158,z8,z17,z6]),(0,[z1,z2,z3,z8,z5,z6,z421]),(0,[z1,z2,z3,z8,z5,z6,z125])],[(0,[z1,z2,z3,z8,z260,z5,z6]),(0,[z1,z2,z3,z8,z5,z422,z6]),(0,[z1,z2,z3,z217,z5,z107,z6]),(0,[z25,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z11,z6,z45]),(0,[z1,z2,z3,z8,z423,z5,z6]),(0,[z1,z424,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z46,z3,z103,z8,z5,z6]),(0,[z1,z2,z425,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z227])],[(0,[z426,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z33,z251,z5,z6]),(0,[z1,z2,z3,z8,z48,z42,z6]),(0,[z1,z2,z3,z8,z48,z241,z6]),(0,[z1,z2,z3,z427,z8,z5,z6])],[(0,[z173,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z428]),(0,[z1,z429,z2,z3,z8,z5,z6])],[(0,[z430,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z36,z8,z11,z6]),(0,[z1,z2,z15,z3,z8,z5,z60]),(0,[z1,z2,z3,z80,z8,z124,z6])],[(0,[z431,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z432,z3,z8,z5,z6]),(0,[z1,z2,z3,z433,z8,z5,z6]),(0,[z1,z2,z3,z434,z8,z5,z6]),(0,[z1,z2,z3,z33,z8,z48,z6]),(0,[z1,z2,z3,z435,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z42,z9]),(0,[z1,z2,z3,z8,z5,z436,z6]),(1,[z1,z2,z3,z8,z290,z6]),(0,[z53,z1,z2,z3,z8,z252,z6]),(0,[z1,z2,z437,z3,z8,z5,z6])],[(0,[z142,z2,z3,z8,z217,z5,z6]),(0,[z93,z1,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z158,z8,z5,z6])],[(0,[z1,z438,z2,z3,z8,z5,z6]),(0,[z1,z10,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z405,z5,z6]),(0,[z439,z1,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z42,z6,z60]),(0,[z1,z2,z3,z8,z5,z16,z60]),(0,[z185,z1,z2,z3,z8,z5,z42]),(0,[z440,z1,z2,z3,z8,z5,z6]),(0,[z1,z194,z2,z182,z3,z8,z6])],[(0,[z1,z2,z3,z8,z441,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z442])]],
   [[(0,[z30,z1,z2,z3,z8,z5,z60]),(0,[z394,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z443,z8,z5,z6]),(1,[z1,z3,z8,z11,z48,z6]),(0,[z1,z2,z3,z444,z8,z5,z6])],[(1,[z1,z300,z3,z8,z5,z6]),(0,[z445,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z99,z5,z6]),(0,[z1,z2,z2,z3,z8,z5,z60]),(0,[z53,z1,z2,z3,z8,z5,z16]),(0,[z53,z1,z2,z3,z8,z17,z5]),(0,[z1,z2,z446,z3,z8,z5,z6]),(0,[z81,z1,z2,z3,z89,z5,z6])],[(0,[z1,z2,z3,z8,z217,z11,z6]),(0,[z32,z1,z2,z3,z33,z5,z6]),(0,[z47,z1,z2,z3,z8,z5,z6]),(0,[z93,z394,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z103,z8,z5,z42]),(1,[z1,z3,z8,z5,z48,z60]),(0,[z325,z1,z2,z3,z8,z5,z60]),(0,[z1,z200,z2,z3,z8,z5,z42]),(0,[z1,z2,z140,z3,z158,z8,z6]),(1,[z70,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z447])],[(0,[z71,z1,z2,z21,z8,z5,z6]),(0,[z25,z1,z2,z3,z8,z11,z6]),(0,[z448,z1,z2,z3,z8,z5,z6]),(0,[z85,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z48,z267,z6]),(0,[z164,z1,z2,z3,z8,z5,z42]),(0,[z53,z221,z2,z3,z8,z5,z6]),(0,[z1,z2,z449,z3,z8,z5,z6])],[(0,[z1,z2,z3,z217,z5,z6,z45]),(0,[z1,z2,z3,z49,z8,z5,z6]),(0,[z1,z450,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z60,z45]),(0,[z1,z194,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z79,z6]),(0,[z91,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z451,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z452]),(0,[z1,z453,z2,z3,z8,z5,z6])],[(0,[z0,z1,z2,z3,z8,z5,z42]),(0,[z1,z454,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z455,z5,z6]),(0,[z2,z3,z8,z159,z5,z68,z6]),(0,[z53,z1,z2,z3,z8,z5,z6])],[(0,[z1,z456,z2,z3,z8,z5,z6]),(0,[z1,z2,z182,z3,z33,z5,z6]),(0,[z1,z2,z3,z457,z8,z5,z6]),(2,[z1,z3,z8,z48,z60]),(0,[z1,z2,z15,z3,z8,z11,z6])]],
   [[(1,[z1,z2,z3,z8,z408,z6]),(0,[z32,z2,z3,z8,z5,z6,z118]),(0,[z1,z458,z2,z3,z8,z5,z6]),(0,[z1,z459,z2,z3,z8,z5,z6]),(0,[z1,z2,z460,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z121,z6]),(0,[z1,z2,z3,z36,z5,z6,z45]),(0,[z1,z2,z140,z3,z8,z124,z6]),(0,[z1,z2,z3,z89,z5,z95,z6])],[(0,[z173,z2,z46,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z242,z5,z6]),(0,[z1,z2,z461,z3,z8,z5,z6]),(0,[z1,z2,z462,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z159,z5,z6]),(0,[z1,z2,z3,z8,z68,z48,z6]),(0,[z1,z2,z3,z463,z8,z5,z6]),(0,[z1,z2,z3,z8,z464,z5,z6])],[(0,[z465,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z314,z6]),(0,[z0,z1,z2,z3,z8,z5,z183]),(0,[z1,z2,z3,z466,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z467,z6]),(0,[z1,z2,z35,z3,z163,z8,z6]),(0,[z1,z2,z303,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z172,z6]),(0,[z1,z2,z3,z8,z5,z6,z468]),(0,[z1,z2,z3,z8,z5,z135,z60]),(0,[z1,z2,z469,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z470,z6])],[(0,[z71,z1,z2,z3,z411,z5,z6]),(0,[z193,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z42,z125])],[(0,[z1,z2,z3,z8,z5,z471,z6]),(0,[z1,z2,z96,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z472]),(0,[z7,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z11,z152,z6]),(0,[z1,z2,z3,z8,z5,z6,z473]),(0,[z1,z109,z2,z140,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z9,z37]),(0,[z474,z1,z2,z3,z8,z5,z6]),(0,[z1,z98,z2,z3,z80,z5,z6]),(0,[z1,z2,z3,z475,z8,z5,z6]),(0,[z1,z476,z2,z3,z8,z5,z6]),(0,[z1,z194,z2,z3,z80,z5,z6]),(0,[z1,z2,z3,z8,z6,z77,z45])]],
   [[(0,[z1,z2,z3,z33,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z477])],[(0,[z478,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z479,z6]),(0,[z1,z2,z3,z8,z5,z6,z480]),(0,[z53,z1,z2,z3,z8,z321,z6])],[(0,[z7,z2,z3,z8,z5,z9,z6]),(0,[z1,z2,z3,z347,z8,z5,z6]),(0,[z481,z1,z2,z3,z8,z5,z6]),(0,[z482,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z483,z8,z5,z6])],[(0,[z1,z2,z3,z8,z283,z5,z6]),(0,[z1,z484,z2,z3,z8,z5,z6]),(0,[z164,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z485,z8,z5,z6])],[(1,[z371,z2,z3,z8,z5,z6]),(0,[z78,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z486,z6])],[(0,[z173,z2,z96,z3,z8,z5,z6]),(0,[z1,z2,z487,z3,z8,z5,z6]),(0,[z1,z10,z2,z3,z8,z5,z240]),(0,[z1,z2,z3,z8,z48,z6,z60]),(0,[z1,z2,z3,z80,z8,z5,z60]),(0,[z1,z2,z3,z488,z8,z5,z6])],[(0,[z0,z1,z2,z3,z8,z48,z6]),(0,[z71,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z489,z8,z5,z6]),(0,[z30,z1,z2,z3,z217,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z490]),(0,[z1,z2,z3,z8,z5,z491,z6]),(0,[z1,z2,z3,z8,z5,z6,z492]),(1,[z1,z2,z376,z8,z5,z6]),(0,[z164,z1,z2,z3,z8,z233,z6])],[(0,[z142,z126,z2,z3,z8,z5,z6]),(0,[z30,z2,z3,z8,z217,z5,z6]),(0,[z1,z3,z8,z11,z5,z48,z6]),(0,[z1,z493,z2,z3,z8,z5,z6]),(0,[z494,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z279,z6])]],
   [[(0,[z1,z450,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z495,z5,z6]),(0,[z305,z1,z2,z3,z8,z5,z64]),(0,[z1,z2,z3,z169,z8,z5,z6]),(0,[z496,z1,z2,z3,z8,z5,z6]),(0,[z497,z1,z2,z3,z8,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z498,z5,z6]),(0,[z1,z2,z3,z8,z217,z5,z42]),(0,[z91,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z16,z118]),(0,[z1,z2,z3,z8,z5,z499,z6]),(0,[z93,z1,z2,z3,z405,z5,z6]),(0,[z305,z1,z2,z3,z8,z11,z6]),(0,[z1,z500,z2,z3,z8,z5,z6])],[(0,[z7,z1,z2,z3,z8,z11,z6]),(0,[z501,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z60,z145]),(0,[z1,z2,z3,z8,z502,z5,z6])],[(0,[z503,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z197]),(0,[z2,z46,z3,z21,z8,z5,z6]),(0,[z1,z2,z3,z217,z251,z5,z6]),(0,[z1,z2,z182,z3,z217,z5,z6]),(0,[z1,z14,z3,z103,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z167]),(0,[z1,z2,z3,z8,z5,z504,z6])],[(0,[z1,z126,z2,z3,z8,z11,z6]),(1,[z71,z2,z21,z8,z5,z6]),(0,[z1,z2,z505,z3,z8,z5,z6]),(0,[z1,z10,z56,z3,z8,z5,z6]),(0,[z396,z1,z2,z3,z8,z5,z6]),(0,[z53,z1,z2,z15,z8,z5,z6])],[(0,[z291,z1,z2,z3,z8,z5,z6]),(0,[z47,z1,z2,z3,z120,z5,z6]),(0,[z1,z2,z3,z8,z5,z118,z37]),(0,[z1,z2,z3,z8,z315,z5,z6]),(0,[z305,z1,z3,z8,z5,z48,z6]),(0,[z1,z2,z3,z506,z5,z48,z6]),(0,[z119,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z35,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z6,z507])],[(0,[z1,z2,z3,z8,z5,z508,z6]),(0,[z1,z2,z3,z8,z5,z6,z64]),(0,[z1,z2,z3,z8,z5,z6,z509])],[(0,[z25,z1,z2,z3,z8,z159,z6]),(0,[z510,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z56,z3,z8,z5,z60]),(0,[z1,z2,z3,z36,z251,z5,z6]),(0,[z193,z1,z511,z3,z8,z5,z6])]],
   [[(0,[z512,z1,z2,z3,z8,z5,z6]),(0,[z1,z513,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z416,z60]),(1,[z396,z1,z2,z3,z8,z5])],[(0,[z1,z2,z514,z3,z8,z5,z6]),(0,[z1,z2,z8,z5,z16,z6,z37]),(0,[z1,z2,z3,z8,z515,z5,z6])],[(0,[z71,z1,z2,z3,z8,z11,z6]),(0,[z516,z1,z2,z3,z8,z5,z6]),(0,[z7,z32,z2,z3,z8,z5,z6]),(0,[z25,z1,z2,z3,z8,z5,z517]),(0,[z85,z69,z2,z3,z8,z5,z6]),(1,[z1,z2,z129,z8,z5,z6]),(0,[z1,z2,z3,z36,z8,z48,z6]),(0,[z518,z1,z2,z3,z8,z11,z6]),(0,[z1,z2,z140,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z225,z60]),(0,[z1,z114,z2,z3,z8,z5,z6]),(0,[z519,z1,z2,z3,z8,z5,z6])],[(0,[z520,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z521]),(0,[z1,z98,z2,z3,z8,z5,z42]),(0,[z1,z2,z522,z3,z8,z48,z6]),(0,[z1,z194,z2,z3,z8,z5,z42]),(0,[z1,z200,z2,z8,z5,z107,z6])],[(0,[z1,z2,z523,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z524]),(0,[z1,z2,z3,z8,z5,z525,z6])],[(1,[z0,z46,z3,z8,z5,z6]),(0,[z526,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z527,z6]),(0,[z1,z2,z3,z8,z5,z9,z16]),(1,[z1,z2,z3,z8,z48,z60]),(0,[z53,z1,z2,z3,z8,z5,z42]),(0,[z1,z2,z528,z3,z8,z5,z6])],[(0,[z529,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z103,z8,z5,z6])],[(0,[z1,z2,z3,z8,z146,z5,z6]),(0,[z1,z2,z3,z8,z5,z530,z6]),(0,[z164,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z163,z8,z6]),(0,[z1,z2,z3,z8,z5,z6,z531])]],
   [[(0,[z1,z2,z3,z33,z104,z5,z6]),(0,[z1,z2,z3,z8,z159,z5,z42]),(0,[z1,z2,z3,z8,z532,z5,z6]),(0,[z1,z2,z3,z8,z11,z42,z6]),(0,[z1,z533,z2,z3,z8,z5,z6])],[(0,[z1,z2,z534,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z217,z48,z6]),(0,[z7,z1,z2,z3,z8,z5,z118]),(0,[z535,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z168,z3,z8,z5,z6]),(0,[z1,z2,z3,z73,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z60,z199]),(0,[z1,z2,z3,z8,z5,z6,z43])],[(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z9,z6]),(0,[z1,z2,z3,z8,z536,z5,z6]),(0,[z1,z10,z2,z3,z8,z346,z6]),(0,[z1,z2,z3,z8,z5,z42,z60]),(0,[z1,z2,z3,z8,z5,z537,z6])],[(0,[z1,z2,z3,z80,z217,z5,z6]),(0,[z538,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z218,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z539]),(0,[z1,z2,z3,z8,z5,z6,z540])],[(0,[z0,z1,z2,z3,z8,z408,z6]),(0,[z1,z2,z3,z541,z8,z5,z6]),(0,[z542,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z543]),(0,[z1,z544,z2,z3,z8,z5,z6])],[(0,[z32,z2,z3,z33,z8,z5,z6]),(0,[z25,z1,z2,z3,z8,z68,z6]),(0,[z1,z98,z2,z3,z8,z5,z201]),(0,[z1,z151,z2,z3,z8,z5,z468]),(0,[z1,z2,z3,z8,z5,z471,z42]),(0,[z81,z397,z2,z3,z8,z5,z6])],[(0,[z545,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z118]),(0,[z93,z1,z2,z3,z8,z5,z327]),(0,[z1,z3,z103,z8,z5,z6,z60]),(0,[z1,z2,z3,z8,z5,z6,z77])],[]],
   [[(1,[z1,z2,z3,z411,z5,z6]),(0,[z546,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z35,z56,z8,z5,z6]),(0,[z547,z1,z2,z3,z8,z5,z6]),(0,[z1,z98,z2,z3,z251,z5,z6]),(0,[z1,z548,z2,z3,z8,z5,z6]),(0,[z397,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z104,z217,z5,z6]),(0,[z1,z2,z549,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z507,z60]),(0,[z1,z2,z3,z8,z550,z5,z6]),(0,[z81,z1,z2,z3,z8,z5,z95])],[(0,[z1,z10,z46,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z17,z5,z9]),(1,[z1,z2,z3,z8,z346,z6]),(0,[z1,z2,z3,z8,z5,z6,z191]),(0,[z1,z2,z3,z8,z5,z551,z42]),(0,[z1,z2,z552,z3,z8,z5,z6]),(0,[z1,z194,z2,z3,z8,z135,z6])],[(0,[z1,z553,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z68,z42]),(0,[z1,z2,z3,z8,z5,z554,z6]),(0,[z1,z555,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z231,z8,z11,z6]),(0,[z1,z2,z3,z556,z8,z5,z6]),(0,[z1,z2,z3,z557,z8,z5,z6]),(0,[z558,z1,z2,z3,z8,z5,z6])],[(0,[z559,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z560,z3,z8,z5,z6]),(0,[z1,z2,z3,z89,z8,z11,z6]),(0,[z1,z2,z3,z89,z5,z107,z6])],[(0,[z1,z2,z46,z3,z8,z5,z60]),(0,[z71,z1,z2,z3,z8,z155,z6]),(0,[z173,z2,z3,z8,z5,z6,z118]),(0,[z561,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z562,z6]),(0,[z1,z2,z3,z36,z8,z5,z6]),(0,[z1,z2,z563,z3,z8,z5,z6])],[(0,[z1,z2,z522,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z564,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z124,z6]),(0,[z1,z109,z2,z3,z8,z11,z6]),(0,[z1,z194,z2,z182,z3,z5,z6])],[(0,[z0,z2,z46,z3,z8,z5,z6]),(0,[z2,z96,z3,z21,z8,z5,z6]),(0,[z565,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z60])],[(0,[z1,z2,z3,z566,z8,z5,z6]),(1,[z1,z2,z3,z506,z48,z6]),(0,[z1,z2,z3,z8,z5,z124,z60]),(0,[z1,z2,z3,z5,z107,z6,z45]),(0,[z1,z109,z2,z158,z8,z5,z6]),(1,[z1,z2,z3,z80,z279,z6])],[(0,[z1,z2,z3,z8,z48,z6,z125]),(0,[z1,z2,z3,z567,z8,z5,z6]),(0,[z1,z2,z3,z8,z568,z5,z6])],[(0,[z1,z2,z569,z3,z8,z5,z6]),(0,[z1,z391,z2,z3,z8,z5,z6]),(0,[z81,z1,z2,z3,z8,z5,z60])],[(0,[z272,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z217,z5,z6]),(0,[z47,z2,z3,z8,z5,z6,z118]),(0,[z93,z1,z2,z3,z8,z5,z250]),(0,[z1,z2,z3,z8,z107,z48,z6]),(0,[z1,z109,z2,z3,z570,z5,z6])],[(0,[z1,z571,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z572]),(0,[z305,z1,z2,z3,z8,z5,z573]),(0,[z574,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z8,z5,z6]),(0,[z575,z1,z2,z3,z8,z5,z6]),(0,[z1,z10,z126,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z576]),(0,[z577,z1,z2,z3,z8,z5,z6]),(0,[z1,z3,z104,z8,z251,z5,z6]),(0,[z578,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z155,z6]),(1,[z1,z2,z3,z8,z390,z6]),(0,[z305,z1,z2,z3,z8,z48,z6]),(0,[z1,z151,z2,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z5,z261,z6]),(0,[z193,z1,z2,z3,z8,z5,z42]),(0,[z579,z1,z2,z3,z8,z5,z6])],[(0,[z0,z1,z2,z352,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z197]),(0,[z1,z2,z96,z3,z8,z5,z60]),(0,[z1,z2,z580,z3,z8,z5,z6]),(0,[z1,z581,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z54,z5,z6])],[(0,[z1,z2,z582,z3,z8,z5,z6]),(0,[z1,z2,z583,z3,z8,z5,z6]),(0,[z1,z56,z3,z103,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z42,z539]),(0,[z1,z2,z3,z8,z5,z584,z6])],[(1,[z1,z2,z3,z8,z343,z6]),(0,[z1,z126,z2,z3,z8,z48,z6]),(0,[z32,z1,z2,z3,z8,z5,z60]),(0,[z1,z10,z3,z8,z5,z6,z60]),(0,[z1,z2,z3,z8,z290,z5,z6]),(0,[z1,z2,z3,z8,z585,z48,z6]),(1,[z1,z303,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z17,z5,z125])],[(1,[z1,z2,z3,z208,z5,z6]),(0,[z1,z10,z2,z56,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z6,z60]),(0,[z1,z2,z3,z8,z5,z6,z586]),(0,[z193,z1,z19,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z42,z118]),(1,[z1,z2,z3,z8,z11,z6]),(0,[z1,z14,z2,z3,z8,z11,z6]),(0,[z1,z13,z2,z3,z8,z11,z6]),(0,[z587,z1,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z8,z5,z51,z6])],[(0,[z588,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z589,z3,z8,z5,z6]),(0,[z590,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z17,z124,z6]),(0,[z1,z2,z511,z3,z8,z5,z6])],[(0,[z1,z591,z2,z3,z8,z5,z6]),(0,[z1,z2,z592,z3,z8,z5,z6]),(0,[z1,z593,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z594,z6]),(0,[z1,z98,z2,z3,z8,z5,z6]),(0,[z595,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z596,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z597]),(0,[z1,z2,z3,z598,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z387,z6]),(0,[z1,z2,z3,z8,z11,z279,z6]),(0,[z1,z2,z182,z3,z8,z5,z60]),(0,[z1,z2,z3,z158,z8,z6,z125])],[(0,[z71,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z573,z6]),(0,[z1,z14,z3,z8,z5,z48,z6]),(0,[z1,z2,z3,z8,z279,z48,z6])],[(0,[z47,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z279,z60]),(0,[z538,z1,z2,z3,z8,z5,z42]),(1,[z1,z2,z3,z570,z5,z6]),(0,[z1,z2,z3,z8,z5,z95,z6])],[(0,[z599,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z600,z6]),(0,[z1,z2,z158,z8,z5,z124,z6]),(0,[z193,z1,z2,z3,z8,z5,z135])],[(0,[z1,z2,z299,z3,z8,z5,z6]),(0,[z142,z1,z2,z3,z8,z5,z42]),(0,[z601,z1,z2,z3,z8,z5,z6]),(0,[z602,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z356,z8,z5,z6])],[(0,[z1,z2,z3,z352,z8,z5,z6]),(0,[z1,z2,z3,z603,z8,z5,z6]),(1,[z1,z3,z8,z48,z6,z60]),(0,[z1,z2,z3,z8,z5,z153,z60])],[(0,[z604,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z605]),(0,[z1,z2,z3,z8,z606,z5,z6]),(0,[z1,z2,z3,z36,z104,z5,z6]),(1,[z1,z2,z3,z506,z5,z6]),(1,[z53,z1,z2,z8,z5,z37]),(0,[z1,z2,z3,z80,z8,z279,z6])],[(0,[z1,z126,z2,z3,z8,z5,z257]),(0,[z1,z2,z56,z21,z8,z5,z6]),(0,[z1,z607,z2,z3,z8,z5,z6]),(0,[z30,z1,z2,z3,z8,z11,z6]),(1,[z1,z2,z3,z8,z99,z6]),(0,[z287,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z608,z6]),(0,[z1,z2,z3,z609,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z610,z6]),(0,[z1,z2,z2,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z5,z611,z6])],[(0,[z1,z2,z3,z612,z8,z5,z6]),(0,[z93,z1,z10,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z60,z60]),(0,[z1,z2,z3,z8,z5,z6,z613])],[(0,[z1,z2,z3,z8,z5,z6,z257]),(0,[z1,z2,z3,z21,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z614,z6]),(0,[z25,z1,z2,z3,z80,z8,z6]),(0,[z1,z615,z2,z3,z8,z5,z6]),(0,[z616,z1,z2,z3,z8,z5,z6]),(0,[z85,z1,z2,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z11,z5,z60]),(0,[z53,z1,z2,z8,z5,z6,z37]),(0,[z1,z617,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z9,z45]),(0,[z1,z2,z3,z8,z251,z5,z60]),(0,[z1,z2,z3,z8,z618,z5,z6])],[(0,[z1,z2,z96,z56,z8,z5,z6]),(0,[z93,z1,z2,z3,z8,z5,z60]),(0,[z305,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z48,z6]),(0,[z1,z2,z182,z3,z8,z11,z6]),(0,[z1,z2,z182,z3,z5,z107,z6]),(0,[z619,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z356,z5,z6])],[(0,[z1,z2,z3,z8,z5,z620,z6]),(0,[z1,z2,z3,z36,z8,z5,z42]),(1,[z1,z200,z2,z5,z107,z6]),(0,[z1,z2,z3,z8,z5,z621,z6]),(0,[z1,z622,z2,z3,z8,z5,z6]),(0,[z1,z623,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z343,z5,z6]),(0,[z1,z2,z3,z624,z8,z5,z6]),(0,[z1,z2,z3,z8,z625,z5,z6]),(0,[z1,z2,z3,z8,z5,z551,z6]),(1,[z1,z2,z3,z8,z626,z6]),(0,[z1,z14,z2,z3,z8,z626,z6]),(0,[z627,z1,z2,z3,z8,z5,z6])],[(0,[z1,z126,z2,z3,z8,z5,z6]),(0,[z30,z32,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z68,z6]),(0,[z1,z2,z3,z8,z585,z5,z6])]],
   [[(1,[z69,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z261,z6]),(0,[z1,z2,z3,z628,z8,z5,z6])],[(0,[z629,z1,z2,z3,z8,z5,z6]),(0,[z142,z2,z3,z21,z8,z5,z6]),(0,[z32,z1,z2,z3,z217,z5,z6]),(0,[z1,z2,z3,z103,z8,z5,z60]),(0,[z1,z200,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z630,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z631,z6]),(0,[z1,z632,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z633,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z6]),(0,[z1,z2,z3,z8,z245,z48,z6]),(0,[z1,z2,z3,z8,z634,z5,z6]),(0,[z1,z194,z2,z3,z158,z8,z6])],[(0,[z635,z1,z2,z3,z8,z5,z6]),(0,[z91,z1,z194,z2,z3,z8,z6]),(0,[z93,z1,z2,z3,z8,z390,z6]),(0,[z1,z2,z3,z89,z8,z48,z6]),(0,[z1,z2,z636,z3,z8,z5,z6])],[(0,[z142,z1,z2,z3,z8,z48,z6]),(0,[z637,z1,z2,z3,z8,z5,z6]),(0,[z638,z1,z2,z3,z8,z5,z6]),(0,[z1,z639,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z60,z360])],[(0,[z25,z1,z2,z3,z8,z5,z42]),(0,[z640,z1,z2,z3,z8,z5,z6]),(0,[z518,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z395,z5,z60]),(1,[z1,z2,z3,z8,z51,z6]),(0,[z193,z1,z2,z3,z8,z17,z6])],[(0,[z0,z1,z46,z3,z8,z5,z6]),(0,[z1,z2,z3,z21,z8,z11,z6]),(0,[z1,z2,z3,z8,z641,z5,z6]),(0,[z642,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z104,z8,z5,z60]),(0,[z1,z2,z3,z8,z11,z11,z6]),(0,[z1,z2,z643,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z644]),(0,[z1,z2,z3,z8,z5,z645,z6])],[(0,[z1,z2,z3,z8,z5,z517,z6]),(0,[z1,z2,z3,z8,z11,z6,z118]),(0,[z1,z2,z3,z8,z251,z11,z6]),(0,[z1,z98,z2,z3,z104,z5,z6]),(0,[z1,z109,z2,z3,z8,z48,z6]),(0,[z599,z1,z2,z3,z8,z5,z6]),(0,[z646,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z2,z3,z8,z217,z5,z6,z118]),(1,[z1,z2,z3,z8,z387,z6]),(0,[z1,z2,z3,z8,z5,z336,z6]),(0,[z1,z2,z3,z8,z17,z5,z60]),(0,[z1,z2,z3,z8,z5,z647,z6]),(0,[z1,z194,z2,z3,z8,z124,z6]),(0,[z1,z2,z648,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z649,z6]),(0,[z1,z2,z3,z8,z5,z118,z45]),(0,[z1,z98,z3,z104,z8,z5,z6]),(0,[z1,z2,z15,z3,z8,z5,z42]),(0,[z1,z2,z3,z650,z8,z5,z6])],[(1,[z1,z2,z299,z8,z5,z6]),(0,[z1,z244,z2,z3,z8,z217,z6]),(0,[z1,z244,z2,z3,z8,z5,z6]),(0,[z2,z3,z8,z5,z9,z6,z118]),(1,[z1,z3,z8,z5,z42,z60]),(0,[z350,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z651,z6]),(0,[z1,z2,z652,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z653])],[(1,[z1,z2,z3,z8,z5,z517]),(1,[z1,z2,z3,z8,z11,z42]),(0,[z1,z2,z3,z80,z8,z11,z6]),(0,[z1,z2,z3,z8,z5,z60,z382]),(0,[z1,z2,z3,z80,z5,z107,z6]),(0,[z193,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z654,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z159,z124,z6]),(0,[z1,z2,z655,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z626,z5,z6])],[(1,[z1,z2,z3,z8,z314,z6]),(0,[z1,z2,z656,z3,z8,z5,z6]),(0,[z1,z2,z3,z506,z8,z48,z6]),(0,[z657,z1,z2,z3,z8,z5,z6])],[(0,[z658,z1,z2,z3,z8,z5,z6]),(0,[z93,z1,z2,z56,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z61,z6]),(0,[z1,z151,z2,z3,z8,z48,z6]),(1,[z1,z14,z3,z8,z5,z42]),(0,[z1,z659,z2,z3,z8,z5,z6])]],
   [[(0,[z71,z1,z2,z3,z8,z5,z79]),(0,[z1,z2,z3,z8,z5,z5,z6]),(0,[z25,z1,z2,z3,z205,z5,z6]),(0,[z85,z1,z98,z3,z8,z5,z6]),(0,[z660,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z42,z473]),(0,[z1,z200,z2,z35,z8,z5,z6]),(0,[z1,z2,z3,z8,z661,z5,z6])],[(0,[z587,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z374,z8,z5,z6]),(0,[z662,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z395,z11,z6]),(0,[z1,z2,z3,z8,z5,z6,z281])],[(0,[z663,z1,z2,z3,z8,z5,z6]),(0,[z664,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z104,z8,z11,z6]),(0,[z1,z2,z3,z104,z5,z107,z6]),(1,[z1,z2,z3,z8,z5,z573]),(1,[z305,z1,z3,z8,z48,z6]),(0,[z1,z3,z8,z5,z48,z6,z60]),(0,[z1,z188,z2,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z11,z6,z125]),(0,[z1,z2,z15,z3,z8,z5,z37]),(0,[z1,z2,z3,z665,z8,z5,z6])],[(0,[z0,z1,z126,z3,z8,z5,z6]),(0,[z1,z2,z666,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z667,z5,z6]),(0,[z1,z2,z3,z36,z33,z5,z6]),(0,[z1,z2,z668,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z108,z6]),(0,[z669,z1,z2,z3,z8,z5,z6])],[(0,[z1,z14,z2,z3,z8,z48,z6]),(0,[z119,z1,z2,z3,z8,z11,z6]),(0,[z1,z2,z35,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z17,z11,z6]),(0,[z164,z1,z3,z8,z5,z6,z60]),(0,[z1,z2,z35,z3,z5,z107,z6]),(0,[z1,z2,z3,z670,z8,z5,z6]),(0,[z1,z2,z3,z5,z95,z6,z45])],[(0,[z1,z2,z3,z8,z5,z6,z671]),(0,[z25,z1,z2,z3,z8,z48,z6]),(0,[z672,z1,z2,z3,z8,z5,z6])],[(0,[z673,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z56,z3,z8,z11,z6])],[(0,[z1,z2,z3,z8,z48,z9,z6]),(1,[z1,z2,z3,z8,z315,z6]),(0,[z1,z2,z207,z3,z8,z11,z6]),(0,[z1,z2,z3,z674,z8,z5,z6]),(0,[z1,z2,z3,z89,z8,z5,z6])]],
   [[(0,[z142,z1,z2,z3,z8,z5,z6]),(0,[z173,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z675,z8,z5,z6]),(0,[z1,z194,z2,z3,z8,z279,z6])],[(0,[z1,z2,z3,z8,z676,z5,z6]),(0,[z1,z2,z15,z3,z8,z48,z6]),(0,[z1,z2,z140,z3,z8,z11,z6]),(0,[z1,z2,z3,z36,z89,z5,z6])],[(0,[z1,z2,z3,z677,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z678,z6]),(0,[z1,z2,z3,z8,z5,z6,z179]),(0,[z1,z2,z3,z8,z5,z135,z42]),(0,[z1,z2,z679,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z54,z5,z6])],[(0,[z1,z2,z3,z8,z48,z6,z118]),(0,[z305,z1,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z8,z5,z48,z42]),(0,[z1,z2,z3,z158,z8,z5,z60]),(0,[z1,z2,z3,z8,z111,z5,z6]),(0,[z1,z109,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z321,z6]),(0,[z680,z1,z2,z3,z8,z5,z6])],[(0,[z7,z1,z2,z3,z8,z5,z42]),(1,[z94,z2,z3,z8,z5,z6]),(0,[z1,z10,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z147,z6]),(0,[z681,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z682,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z208,z5,z6]),(1,[z1,z2,z3,z8,z5,z468]),(0,[z1,z2,z3,z122,z8,z5,z6]),(0,[z683,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z252,z5,z6]),(0,[z1,z2,z3,z8,z5,z684,z6])],[(0,[z1,z2,z3,z685,z8,z5,z6]),(0,[z1,z126,z2,z3,z8,z5,z42]),(0,[z1,z2,z686,z3,z8,z5,z6]),(0,[z30,z1,z2,z3,z8,z48,z6]),(0,[z85,z1,z2,z3,z251,z5,z6]),(0,[z1,z2,z3,z8,z687,z5,z6]),(0,[z1,z2,z3,z8,z5,z107,z6]),(0,[z1,z2,z3,z8,z5,z6,z688])],[(0,[z47,z7,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z201,z6]),(0,[z1,z2,z2,z3,z8,z48,z6]),(1,[z1,z14,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z60,z125])]],
   [[(0,[z689,z1,z2,z3,z8,z5,z6]),(0,[z47,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z6,z210]),(0,[z1,z2,z3,z8,z48,z554,z6]),(1,[z1,z151,z3,z8,z5,z60]),(0,[z1,z2,z3,z690,z8,z5,z6]),(0,[z691,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z692,z5,z6]),(0,[z93,z1,z3,z103,z8,z5,z6]),(0,[z85,z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z6,z693])],[(0,[z694,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z695]),(0,[z1,z2,z376,z3,z8,z5,z6]),(0,[z1,z98,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z506,z8,z5,z6]),(0,[z1,z194,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z80,z36,z5,z6]),(0,[z696,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z17,z5,z118]),(0,[z1,z697,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z698,z6]),(0,[z1,z98,z2,z182,z3,z5,z6]),(0,[z1,z151,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z699,z8,z5,z6]),(0,[z1,z2,z3,z8,z570,z5,z6]),(0,[z1,z2,z3,z134,z8,z5,z6])],[(0,[z2,z46,z3,z8,z217,z5,z6]),(0,[z71,z1,z2,z3,z8,z5,z42]),(0,[z173,z1,z2,z3,z8,z11,z6]),(1,[z30,z2,z3,z217,z5,z6]),(0,[z53,z1,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z348,z6])],[(0,[z91,z2,z3,z8,z5,z68,z6]),(0,[z1,z2,z3,z8,z5,z6,z700]),(0,[z1,z2,z3,z8,z92,z5,z6]),(0,[z1,z2,z3,z8,z701,z5,z6]),(0,[z662,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z140,z8,z5,z124,z6]),(1,[z221,z2,z3,z8,z5,z6]),(0,[z193,z1,z2,z15,z3,z8,z5]),(1,[z81,z1,z2,z3,z5,z45]),(0,[z1,z2,z3,z8,z5,z6,z702])],[(0,[z173,z1,z2,z96,z8,z5,z6]),(0,[z703,z1,z2,z3,z8,z5,z6]),(1,[z1,z194,z2,z182,z3,z6]),(1,[z1,z511,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z704,z6]),(0,[z1,z2,z3,z8,z5,z705,z6]),(0,[z1,z2,z3,z36,z217,z5,z6]),(0,[z1,z2,z3,z8,z159,z5,z60]),(0,[z371,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z158,z8,z11,z6]),(0,[z706,z1,z2,z3,z8,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z8,z5,z707]),(0,[z1,z3,z8,z11,z412,z6]),(0,[z1,z10,z103,z8,z5,z60]),(0,[z325,z1,z2,z3,z8,z199]),(0,[z221,z2,z3,z8,z5,z42]),(0,[z708,z2,z3,z8,z5,z6]),(0,[z53,z1,z2,z8,z321,z37])],[(0,[z1,z2,z3,z242,z11,z6]),(0,[z1,z194,z2,z182,z3,z42]),(0,[z1,z511,z3,z8,z5,z42]),(0,[z709,z2,z3,z8,z5,z6])],[(0,[z1,z2,z352,z208,z5,z6]),(0,[z1,z224,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z710,z6]),(0,[z711,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z712,z6])],[(0,[z1,z2,z3,z8,z5,z713]),(0,[z71,z2,z714,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z179]),(0,[z1,z2,z715,z3,z8,z6]),(0,[z1,z2,z3,z8,z51,z6]),(1,[z1,z716,z3,z8,z5]),(0,[z1,z2,z3,z8,z645,z135])],[(0,[z1,z2,z3,z717,z5,z6]),(0,[z1,z2,z3,z8,z718,z6]),(0,[z1,z719,z3,z8,z5,z6]),(0,[z1,z14,z3,z73,z48,z6]),(0,[z263,z2,z3,z5,z6,z45])],[(0,[z1,z720,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z721,z6]),(0,[z1,z98,z3,z104,z48,z6]),(0,[z1,z3,z8,z5,z42,z477])],[(0,[z1,z2,z3,z49,z5,z42]),(0,[z85,z1,z3,z251,z11,z6]),(0,[z1,z194,z3,z8,z48,z60])],[(0,[z1,z2,z3,z8,z5,z183]),(0,[z1,z2,z3,z8,z5,z722]),(0,[z1,z2,z3,z8,z11,z250])],[(0,[z1,z2,z3,z8,z5,z723]),(0,[z724,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z725]),(0,[z1,z2,z3,z8,z726,z6]),(0,[z1,z2,z35,z36,z11,z6])],[(0,[z1,z2,z3,z8,z5,z727]),(1,[z1,z3,z506,z48,z60]),(0,[z1,z2,z3,z8,z728,z6])],[(0,[z1,z2,z3,z8,z48,z257]),(0,[z1,z3,z729,z251,z5,z6]),(0,[z1,z2,z3,z8,z99,z167]),(0,[z662,z2,z3,z8,z171,z6]),(0,[z1,z3,z8,z48,z42,z60])],[(0,[z1,z2,z3,z730,z5,z6]),(0,[z394,z2,z3,z49,z5,z6]),(0,[z1,z2,z3,z8,z346,z60]),(0,[z1,z2,z3,z8,z731,z6]),(0,[z1,z544,z3,z8,z48,z6]),(0,[z1,z511,z3,z8,z5,z135])],[(0,[z1,z2,z3,z732,z5,z6]),(0,[z733,z2,z3,z8,z5,z6]),(0,[z53,z1,z511,z3,z8,z5])],[(0,[z272,z2,z3,z8,z121,z6])],[(0,[z1,z2,z3,z8,z734,z6]),(0,[z1,z10,z56,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z735])]],
   [[(0,[z1,z2,z3,z8,z5,z736]),(0,[z2,z3,z8,z5,z737,z118]),(0,[z394,z2,z3,z8,z11,z6]),(0,[z1,z10,z3,z8,z5,z60]),(0,[z397,z2,z3,z8,z11,z6])],[(0,[z1,z2,z3,z738,z5,z6]),(1,[z1,z2,z5,z739,z6])],[(0,[z1,z2,z3,z92,z5,z42]),(0,[z1,z2,z3,z740,z8,z6]),(0,[z1,z3,z8,z48,z507,z60])],[(0,[z1,z2,z3,z8,z48,z6]),(0,[z1,z2,z741,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z742]),(0,[z1,z2,z3,z8,z5,z743]),(0,[z1,z2,z3,z744,z5,z6]),(0,[z2,z3,z8,z5,z6,z745]),(0,[z1,z263,z2,z3,z5,z45])],[(0,[z1,z2,z3,z8,z5,z746]),(0,[z93,z1,z103,z8,z11,z6]),(0,[z1,z2,z3,z8,z747,z6]),(0,[z1,z2,z3,z8,z5,z748]),(0,[z1,z98,z3,z414,z5,z6]),(0,[z1,z109,z3,z8,z48,z60]),(0,[z1,z2,z3,z80,z279,z60]),(0,[z749,z2,z3,z8,z5,z6])],[(0,[z30,z2,z3,z750,z5,z6]),(0,[z1,z97,z3,z8,z5,z42]),(0,[z751,z2,z3,z8,z5,z6]),(1,[z263,z2,z3,z5,z45])],[(0,[z1,z2,z3,z169,z158,z6]),(0,[z1,z2,z3,z8,z5,z752])],[(0,[z753,z46,z3,z8,z5,z6]),(0,[z69,z2,z3,z104,z5,z6]),(0,[z1,z329,z2,z182,z3,z6])],[(0,[z1,z2,z3,z8,z5,z754])],[(0,[z1,z2,z3,z755,z11,z6]),(0,[z1,z2,z3,z8,z6,z756])],[(0,[z1,z2,z3,z8,z5,z757]),(0,[z1,z460,z3,z8,z5,z60]),(0,[z1,z98,z3,z104,z5,z6]),(0,[z1,z2,z758,z8,z5,z6]),(0,[z1,z2,z3,z8,z759,z6])],[(0,[z1,z244,z2,z3,z8,z6]),(0,[z69,z2,z129,z8,z5,z6]),(0,[z1,z2,z3,z54,z5,z60])],[(0,[z1,z2,z3,z760,z8,z6]),(0,[z81,z1,z3,z8,z48,z60]),(0,[z672,z1,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z761])],[(0,[z1,z2,z3,z8,z343,z60]),(0,[z69,z2,z3,z8,z5,z210]),(0,[z1,z2,z3,z8,z252,z6]),(0,[z1,z762,z3,z8,z5,z6])],[(0,[z1,z2,z3,z763,z5,z6]),(0,[z1,z2,z3,z236,z11,z6]),(0,[z1,z2,z3,z48,z6,z764])],[(0,[z1,z2,z3,z8,z5,z257]),(0,[z1,z2,z352,z8,z5,z183]),(0,[z706,z2,z3,z8,z5,z118]),(0,[z263,z2,z3,z8,z48,z6]),(0,[z221,z2,z3,z8,z5,z16]),(0,[z221,z2,z3,z8,z17,z5])]],
   [[(0,[z1,z2,z3,z8,z5,z765])],[(0,[z1,z109,z2,z169,z158,z6]),(0,[z1,z2,z3,z8,z5,z766]),(0,[z1,z2,z3,z5,z6,z767])],[(0,[z292,z2,z3,z8,z5,z9]),(0,[z1,z109,z2,z158,z570,z6])],[(0,[z768,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z6,z769]),(0,[z2,z3,z8,z770,z68,z6]),(0,[z1,z2,z3,z771,z5,z6]),(0,[z1,z14,z3,z8,z5,z227]),(0,[z1,z2,z140,z8,z772,z6])],[(0,[z773,z1,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z774]),(0,[z1,z2,z3,z8,z387,z42])],[(0,[z1,z2,z3,z8,z5,z6]),(0,[z7,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z775,z5,z6]),(0,[z1,z168,z3,z8,z48,z60]),(0,[z1,z3,z488,z8,z5,z60]),(0,[z776,z2,z3,z8,z5,z42]),(0,[z70,z2,z3,z54,z5,z6])],[(0,[z0,z46,z299,z8,z5,z6])],[(0,[z32,z2,z3,z33,z5,z6]),(0,[z47,z2,z3,z8,z48,z118]),(0,[z1,z2,z3,z8,z99,z60]),(0,[z1,z777,z3,z8,z5,z6])],[(0,[z1,z2,z352,z8,z48,z6]),(0,[z1,z2,z3,z8,z11,z20]),(0,[z1,z300,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z48,z240])],[(0,[z1,z2,z3,z778,z5,z6]),(0,[z1,z2,z3,z80,z649,z6]),(0,[z1,z2,z3,z8,z48,z143]),(0,[z164,z1,z3,z8,z261,z60]),(0,[z1,z2,z3,z8,z5,z52])],[(0,[z0,z46,z3,z8,z314,z6]),(0,[z779,z2,z3,z8,z5,z6]),(0,[z1,z2,z8,z772,z124,z6])],[(0,[z1,z2,z3,z8,z5,z780]),(0,[z1,z220,z3,z8,z11,z6]),(0,[z1,z3,z8,z261,z6,z60])],[(0,[z1,z2,z3,z120,z48,z6]),(0,[z1,z2,z3,z8,z781,z6]),(0,[z1,z2,z3,z80,z568,z6])],[(0,[z25,z1,z3,z8,z48,z60]),(0,[z1,z2,z3,z782,z5,z6]),(0,[z1,z3,z506,z5,z48,z60]),(0,[z1,z2,z3,z169,z5,z42]),(0,[z1,z533,z2,z5,z107,z6]),(0,[z221,z2,z3,z8,z321,z6])]],
   [[(0,[z300,z3,z21,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z783]),(0,[z510,z1,z2,z8,z5,z37])],[(0,[z1,z2,z3,z8,z784,z6]),(0,[z1,z2,z3,z80,z205,z6]),(0,[z785,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z48,z210]),(0,[z1,z230,z2,z5,z107,z6]),(0,[z1,z2,z3,z8,z786,z6])],[(0,[z1,z787,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z315,z250]),(0,[z1,z3,z8,z48,z6,z613]),(0,[z1,z3,z8,z330,z11,z6]),(0,[z1,z2,z3,z8,z788,z6])],[(0,[z1,z2,z3,z8,z155,z88]),(0,[z263,z2,z3,z8,z5,z6]),(0,[z69,z2,z182,z3,z5,z6]),(0,[z1,z2,z3,z8,z6,z789]),(0,[z790,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z80,z66,z6])],[(0,[z1,z2,z3,z8,z791,z6]),(0,[z1,z3,z36,z8,z48,z60]),(0,[z1,z2,z3,z792,z5,z42]),(0,[z1,z793,z3,z8,z5,z6])],[(0,[z93,z94,z103,z8,z5,z6]),(0,[z1,z2,z3,z794,z5,z6]),(0,[z1,z522,z3,z8,z48,z60]),(0,[z1,z2,z3,z8,z233,z42]),(0,[z396,z1,z2,z140,z8,z124])],[(0,[z1,z2,z3,z8,z395,z195])],[(0,[z1,z2,z3,z8,z795,z6]),(0,[z1,z2,z3,z8,z5,z796]),(0,[z94,z2,z3,z8,z5,z250]),(0,[z1,z2,z3,z8,z5,z797])],[(0,[z1,z2,z3,z8,z798,z6]),(0,[z69,z2,z3,z8,z290,z6])],[(0,[z1,z2,z3,z8,z5,z799])],[(0,[z673,z46,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z800]),(0,[z91,z2,z3,z8,z68,z42]),(0,[z394,z2,z3,z8,z315,z6]),(0,[z1,z3,z8,z11,z42,z60]),(0,[z1,z2,z643,z5,z107,z6])],[(0,[z1,z300,z3,z8,z5,z801]),(0,[z1,z2,z3,z8,z802,z6])],[(0,[z1,z2,z299,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z803]),(0,[z1,z19,z3,z8,z5,z227]),(0,[z1,z151,z3,z8,z626,z6])],[(0,[z1,z2,z3,z8,z5,z804]),(0,[z47,z2,z3,z8,z5,z118]),(0,[z1,z2,z3,z73,z48,z6]),(0,[z1,z2,z140,z8,z124,z42])],[(0,[z1,z2,z352,z8,z5,z6]),(0,[z93,z1,z103,z8,z315,z6]),(0,[z1,z2,z3,z8,z805,z6]),(0,[z185,z1,z2,z3,z8,z125]),(0,[z1,z511,z15,z3,z8,z5]),(0,[z1,z2,z511,z3,z8,z125])],[(0,[z1,z2,z3,z8,z5,z143]),(0,[z1,z2,z3,z8,z5,z806]),(0,[z1,z697,z3,z8,z5,z42]),(0,[z164,z1,z3,z8,z48,z60]),(0,[z1,z2,z3,z134,z8,z6])]],
   [[(0,[z1,z2,z3,z8,z314,z60]),(0,[z1,z2,z3,z8,z146,z6]),(0,[z1,z484,z2,z5,z107,z6])],[(0,[z1,z659,z3,z8,z5,z60]),(0,[z1,z511,z3,z8,z5,z267])],[(0,[z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z8,z5,z807]),(0,[z1,z255,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z135,z597])],[(0,[z193,z1,z511,z3,z8,z125])],[(0,[z1,z2,z3,z8,z11,z167]),(0,[z305,z1,z3,z8,z48,z60]),(0,[z1,z511,z3,z8,z48,z60]),(0,[z396,z1,z2,z3,z8,z48])],[(0,[z1,z458,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z5,z210]),(0,[z1,z2,z3,z808,z11,z6]),(0,[z1,z424,z3,z8,z11,z6]),(0,[z193,z1,z303,z3,z8,z5])],[(0,[z1,z2,z809,z8,z5,z6]),(0,[z1,z810,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z811,z6]),(0,[z1,z98,z3,z729,z5,z6])],[(0,[z1,z2,z3,z242,z5,z79]),(0,[z1,z2,z3,z8,z48,z88]),(0,[z465,z2,z3,z217,z5,z6]),(0,[z1,z2,z3,z49,z5,z250]),(0,[z1,z3,z8,z5,z812,z60]),(0,[z1,z2,z3,z8,z42,z77])],[(0,[z1,z2,z3,z8,z314,z197]),(0,[z1,z224,z3,z8,z5,z79]),(0,[z1,z813,z3,z8,z5,z6]),(0,[z1,z2,z582,z36,z5,z6]),(0,[z1,z2,z3,z8,z48,z227]),(0,[z392,z1,z3,z8,z5,z60]),(0,[z1,z3,z8,z5,z60,z539]),(0,[z1,z2,z3,z814,z5,z60])],[(0,[z642,z2,z3,z8,z5,z118]),(0,[z1,z188,z2,z347,z8,z6]),(0,[z53,z70,z2,z8,z5,z37])],[(0,[z1,z2,z3,z815,z8,z6]),(0,[z1,z19,z3,z8,z5,z6]),(0,[z1,z151,z3,z8,z11,z42]),(0,[z816,z1,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z283,z6]),(0,[z599,z1,z3,z8,z48,z60])],[(0,[z1,z2,z3,z8,z48,z138]),(0,[z81,z1,z2,z3,z5,z767])],[(0,[z1,z2,z3,z8,z408,z183]),(0,[z1,z2,z207,z8,z152,z6])],[(0,[z0,z46,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z5,z817]),(0,[z94,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z405,z48,z6])],[(0,[z1,z2,z3,z818,z5,z60])]],
   [[(0,[z325,z1,z3,z8,z48,z60])],[(0,[z1,z224,z3,z8,z819,z6]),(0,[z2,z3,z750,z217,z5,z6]),(0,[z1,z2,z3,z205,z5,z6]),(0,[z1,z2,z3,z73,z5,z6]),(0,[z1,z2,z3,z8,z321,z42])],[(0,[z2,z3,z457,z8,z5,z118]),(0,[z1,z615,z3,z8,z5,z60]),(0,[z1,z2,z103,z405,z5,z6]),(0,[z69,z2,z376,z8,z5,z6]),(0,[z1,z2,z3,z8,z147,z42])],[(0,[z93,z1,z103,z49,z5,z6]),(0,[z1,z2,z3,z8,z820,z6]),(0,[z1,z3,z414,z8,z11,z6]),(0,[z164,z1,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z821,z6])],[(0,[z1,z2,z3,z8,z822,z6]),(0,[z161,z1,z3,z8,z5,z60]),(0,[z1,z2,z3,z823,z5,z6]),(0,[z1,z2,z3,z824,z5,z6]),(0,[z1,z825,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z826]),(0,[z1,z2,z3,z8,z5,z827]),(0,[z828,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z829,z6])],[(0,[z30,z2,z3,z217,z5,z60])],[(0,[z1,z2,z3,z8,z5,z830]),(0,[z1,z2,z3,z8,z146,z240])],[(0,[z71,z2,z21,z8,z155,z6]),(0,[z1,z2,z3,z8,z831,z6]),(0,[z1,z2,z3,z8,z832,z6]),(0,[z1,z2,z3,z8,z5,z833]),(0,[z2,z3,z8,z48,z6,z745]),(0,[z1,z3,z8,z48,z60,z125]),(0,[z1,z194,z2,z182,z3,z60])],[(0,[z1,z2,z3,z834,z5,z6]),(0,[z1,z2,z3,z411,z11,z6]),(0,[z1,z835,z3,z8,z5,z6]),(0,[z305,z1,z3,z506,z48,z6])],[(0,[z1,z836,z2,z3,z8,z6]),(0,[z1,z2,z3,z5,z60,z764]),(0,[z837,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z838,z5,z6])],[(0,[z1,z2,z3,z8,z5,z88]),(0,[z1,z2,z3,z242,z5,z42]),(0,[z1,z2,z3,z8,z839,z6]),(0,[z1,z3,z8,z48,z6,z695]),(0,[z1,z2,z3,z8,z840,z6]),(0,[z538,z1,z2,z8,z5,z473]),(0,[z1,z2,z3,z8,z111,z135]),(0,[z263,z2,z3,z8,z5,z95])],[(0,[z1,z224,z3,z8,z5,z42]),(0,[z1,z841,z2,z3,z8,z6]),(0,[z85,z371,z3,z251,z5,z6]),(0,[z1,z2,z3,z8,z5,z227]),(0,[z263,z2,z3,z8,z5,z45])],[(0,[z1,z842,z3,z8,z5,z6]),(0,[z1,z2,z3,z843,z8,z6])],[(0,[z1,z3,z8,z68,z48,z60]),(0,[z1,z2,z3,z49,z5,z60]),(0,[z1,z14,z3,z8,z346,z6]),(0,[z1,z2,z3,z8,z5,z844]),(0,[z1,z2,z3,z8,z17,z175]),(0,[z53,z1,z114,z8,z5,z37])],[(0,[z1,z2,z299,z4,z5,z6]),(0,[z1,z2,z3,z8,z387,z167]),(0,[z599,z1,z3,z8,z5,z60])]],
   [[(0,[z1,z2,z3,z8,z290,z6]),(0,[z1,z2,z3,z8,z5,z138]),(0,[z1,z2,z3,z8,z17,z195])],[(0,[z94,z2,z56,z8,z5,z6]),(0,[z85,z1,z3,z251,z5,z42]),(0,[z1,z2,z3,z506,z279,z6]),(0,[z1,z2,z3,z8,z5,z845]),(0,[z1,z2,z3,z8,z5,z846])],[(0,[z1,z2,z847,z8,z5,z6]),(0,[z1,z2,z3,z8,z848,z6]),(0,[z1,z2,z3,z405,z5,z6]),(0,[z1,z2,z3,z8,z11,z60])],[(0,[z1,z2,z3,z4,z314,z6]),(0,[z1,z2,z3,z8,z48,z327]),(0,[z1,z2,z35,z36,z5,z42]),(0,[z1,z194,z511,z3,z8,z6])],[(0,[z1,z2,z3,z849,z5,z6]),(0,[z371,z2,z3,z8,z48,z6]),(0,[z1,z3,z8,z11,z48,z6]),(1,[z1,z2,z3,z8,z850])],[(0,[z365,z2,z3,z217,z5,z6]),(0,[z1,z2,z3,z49,z390,z6]),(0,[z209,z1,z3,z8,z5,z60]),(0,[z1,z149,z2,z5,z107,z6]),(0,[z1,z3,z8,z618,z5,z60]),(0,[z1,z2,z3,z851,z5,z6])],[(0,[z546,z46,z3,z8,z5,z6]),(0,[z1,z2,z376,z8,z48,z6]),(1,[z1,z3,z73,z48,z60])],[(0,[z1,z2,z3,z8,z11,z852]),(0,[z1,z2,z3,z570,z5,z60])],[(0,[z0,z1,z3,z8,z48,z60]),(0,[z1,z3,z8,z5,z551,z60]),(0,[z1,z303,z3,z54,z5,z6])],[(0,[z1,z853,z3,z8,z5,z6]),(0,[z1,z2,z3,z205,z5,z143]),(0,[z1,z2,z3,z92,z5,z60])],[(0,[z1,z2,z3,z8,z11,z197]),(0,[z2,z3,z217,z5,z6,z179]),(0,[z1,z2,z3,z8,z854,z6]),(0,[z394,z2,z3,z8,z5,z42]),(0,[z397,z2,z3,z8,z5,z42])],[(0,[z1,z2,z855,z8,z5,z6]),(0,[z1,z2,z3,z856,z5,z6]),(0,[z1,z2,z3,z729,z5,z6]),(1,[z1,z3,z8,z261,z60])],[(0,[z1,z2,z3,z8,z408,z6]),(0,[z1,z2,z3,z8,z857,z6]),(0,[z71,z2,z21,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z858]),(0,[z74,z1,z3,z8,z48,z6]),(0,[z1,z303,z3,z8,z11,z6])],[(0,[z1,z2,z3,z208,z11,z6]),(0,[z1,z389,z3,z8,z48,z6]),(0,[z1,z511,z3,z8,z5,z9])],[(0,[z93,z1,z103,z8,z5,z42]),(0,[z662,z1,z2,z3,z506,z6]),(0,[z70,z2,z3,z8,z11,z6]),(0,[z1,z3,z8,z5,z60,z473]),(0,[z1,z3,z8,z5,z60,z613]),(0,[z1,z2,z8,z5,z6,z859])],[(0,[z385,z1,z103,z8,z5,z6]),(0,[z1,z2,z129,z251,z5,z6]),(0,[z1,z3,z8,z395,z48,z6])]],
   [[(0,[z1,z300,z3,z8,z5,z79]),(0,[z1,z2,z3,z8,z860,z6]),(0,[z1,z3,z8,z5,z645,z60]),(0,[z1,z511,z3,z8,z6,z125])],[(0,[z1,z2,z3,z8,z861,z6])],[(0,[z32,z2,z3,z750,z5,z6]),(0,[z1,z2,z129,z8,z48,z6]),(0,[z1,z200,z2,z5,z107,z60])],[(0,[z1,z2,z3,z862,z5,z6]),(0,[z94,z3,z103,z8,z5,z6]),(0,[z1,z103,z8,z5,z225,z60]),(0,[z185,z1,z2,z3,z8,z539])],[(0,[z1,z2,z3,z8,z5,z863]),(0,[z1,z2,z3,z33,z5,z179]),(0,[z1,z114,z3,z54,z5,z6])],[(0,[z1,z2,z3,z8,z5,z864]),(0,[z430,z1,z3,z8,z48,z6])],[(0,[z865,z2,z3,z8,z5,z60])],[(0,[z1,z654,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z327]),(0,[z1,z2,z3,z506,z11,z6]),(0,[z44,z1,z3,z8,z5,z60])],[(0,[z371,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z236,z5,z42]),(0,[z1,z2,z3,z8,z866,z6]),(0,[z1,z2,z3,z867,z5,z6]),(0,[z1,z2,z3,z8,z868,z6])],[(0,[z1,z2,z3,z8,z5,z869]),(0,[z1,z2,z3,z311,z8,z42])],[(0,[z1,z2,z3,z8,z870,z6]),(0,[z1,z2,z376,z8,z5,z6]),(0,[z1,z3,z8,z661,z5,z60])],[(0,[z535,z1,z2,z3,z5,z45]),(0,[z1,z2,z3,z80,z232,z6])],[],[(0,[z1,z2,z3,z8,z5,z871]),(0,[z1,z2,z3,z8,z5,z872]),(0,[z2,z3,z8,z5,z873,z6]),(0,[z1,z2,z3,z8,z387,z60]),(0,[z1,z2,z3,z356,z11,z6])],[(0,[z1,z2,z3,z92,z5,z9]),(0,[z1,z2,z3,z8,z290,z210]),(0,[z1,z2,z3,z8,z348,z6]),(0,[z1,z2,z3,z8,z874,z6])],[(0,[z1,z2,z3,z8,z283,z88]),(0,[z1,z875,z3,z8,z5,z6]),(0,[z1,z10,z3,z8,z346,z60]),(1,[z1,z3,z8,z48,z60]),(0,[z1,z2,z3,z5,z6,z876])]],
   [[(0,[z71,z2,z21,z8,z5,z6])],[(0,[z1,z2,z3,z877,z5,z6]),(0,[z173,z1,z3,z8,z48,z60]),(0,[z1,z3,z8,z48,z9,z60]),(0,[z1,z2,z3,z8,z5,z240]),(0,[z69,z2,z3,z8,z11,z6]),(0,[z85,z69,z3,z251,z5,z6])],[(0,[z1,z2,z3,z8,z5,z878]),(0,[z1,z2,z3,z8,z5,z879])],[(0,[z1,z2,z352,z8,z408,z6]),(0,[z309,z2,z3,z33,z5,z6]),(0,[z1,z438,z3,z8,z5,z60])],[(0,[z1,z2,z3,z880,z8,z6]),(0,[z1,z300,z3,z8,z5,z42]),(0,[z1,z2,z3,z92,z5,z118]),(0,[z1,z14,z3,z8,z5,z812])],[(0,[z1,z2,z3,z120,z5,z6])],[(0,[z1,z2,z129,z8,z5,z6]),(0,[z53,z1,z2,z356,z5,z37])],[(0,[z1,z2,z299,z8,z5,z197]),(0,[z1,z2,z3,z8,z5,z881]),(0,[z1,z2,z3,z134,z107,z6]),(0,[z1,z2,z3,z8,z882,z6])],[(0,[z291,z1,z3,z8,z48,z60]),(0,[z1,z109,z2,z158,z8,z6])],[(0,[z1,z2,z3,z8,z5,z883]),(0,[z1,z2,z3,z8,z772,z6]),(0,[z1,z2,z884,z8,z5,z6])],[(0,[z1,z2,z299,z208,z5,z6]),(0,[z1,z885,z3,z8,z5,z6]),(0,[z1,z2,z3,z886,z5,z6]),(0,[z1,z887,z3,z8,z5,z6])],[(0,[z53,z1,z303,z8,z5,z37])],[(0,[z1,z2,z3,z8,z5,z888]),(0,[z1,z2,z3,z8,z315,z60]),(0,[z1,z2,z3,z8,z889,z6]),(0,[z1,z2,z3,z8,z233,z60]),(0,[z193,z1,z2,z3,z8,z125])],[(0,[z1,z2,z3,z8,z5,z890])],[(0,[z1,z2,z3,z208,z314,z6]),(0,[z1,z2,z3,z8,z5,z891]),(0,[z1,z2,z3,z8,z5,z892])],[(0,[z1,z2,z3,z8,z172,z42]),(0,[z1,z3,z8,z48,z118,z60])]],
   [[(0,[z32,z2,z3,z28,z5,z6]),(0,[z1,z317,z3,z8,z48,z6]),(0,[z1,z2,z3,z893,z48,z6]),(0,[z193,z1,z2,z3,z506,z6]),(0,[z1,z2,z3,z8,z111,z267])],[(0,[z91,z2,z3,z8,z68,z60]),(0,[z1,z2,z129,z80,z5,z6]),(0,[z894,z2,z3,z8,z5,z6]),(0,[z85,z1,z3,z251,z147,z6]),(0,[z1,z2,z3,z54,z48,z6]),(0,[z1,z27,z3,z8,z5,z42])],[(0,[z1,z2,z3,z8,z895,z6]),(0,[z1,z10,z3,z8,z5,z257]),(0,[z1,z2,z3,z8,z896,z6])],[(0,[z1,z2,z3,z8,z5,z897]),(0,[z1,z2,z898,z8,z5,z6])],[(0,[z1,z2,z3,z899,z5,z6]),(0,[z2,z3,z714,z8,z5,z6]),(0,[z1,z2,z3,z8,z900,z6]),(0,[z1,z244,z2,z182,z3,z6]),(0,[z1,z2,z3,z8,z5,z901]),(0,[z1,z2,z140,z8,z124,z60]),(0,[z1,z109,z2,z8,z772,z6])],[(0,[z1,z224,z3,z242,z5,z6]),(0,[z902,z2,z3,z8,z5,z6]),(0,[z1,z13,z2,z218,z3,z6]),(0,[z1,z2,z3,z8,z135,z850])],[(0,[z1,z2,z3,z903,z5,z6]),(0,[z1,z2,z3,z8,z346,z6]),(0,[z371,z2,z3,z8,z5,z210])],[(0,[z1,z3,z8,z5,z826,z60])],[(0,[z1,z2,z3,z904,z5,z6]),(0,[z94,z2,z3,z8,z390,z6]),(0,[z1,z2,z376,z8,z5,z210])],[(0,[z1,z905,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z290,z138]),(0,[z1,z3,z73,z11,z48,z6])],[(0,[z1,z2,z3,z8,z5,z906]),(0,[z221,z2,z3,z8,z5,z60])],[(0,[z47,z2,z3,z120,z5,z118]),(0,[z1,z3,z8,z72,z48,z60]),(0,[z1,z511,z3,z8,z5,z60]),(0,[z1,z632,z3,z8,z5,z60]),(0,[z1,z2,z3,z54,z252,z6])],[(0,[z1,z2,z3,z4,z5,z42]),(0,[z1,z2,z3,z8,z907,z6]),(0,[z1,z596,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z6,z850])],[(0,[z1,z3,z80,z8,z48,z60])],[(0,[z1,z2,z3,z8,z5,z908]),(0,[z1,z2,z3,z782,z346,z6]),(0,[z1,z2,z129,z104,z5,z6]),(0,[z1,z2,z110,z8,z5,z551]),(0,[z1,z2,z3,z80,z279,z6])],[(0,[z1,z2,z3,z8,z5,z909]),(0,[z1,z2,z3,z8,z343,z257]),(0,[z1,z2,z3,z411,z5,z79])]],
   [[(0,[z1,z2,z3,z8,z910,z6]),(0,[z1,z2,z3,z8,z5,z911]),(0,[z193,z1,z2,z3,z8,z321])],[(0,[z1,z151,z3,z8,z11,z60]),(0,[z1,z3,z8,z5,z60,z55]),(0,[z1,z14,z3,z8,z626,z42]),(0,[z912,z2,z3,z8,z5,z6])],[(0,[z173,z2,z3,z8,z5,z88]),(0,[z1,z303,z3,z8,z17,z5])],[(0,[z59,z2,z3,z8,z5,z153]),(0,[z1,z3,z105,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z913])],[(0,[z71,z2,z21,z8,z283,z6]),(0,[z1,z2,z3,z914,z5,z6]),(0,[z1,z2,z129,z8,z5,z210]),(0,[z1,z2,z3,z8,z5,z915]),(0,[z1,z2,z3,z893,z5,z6]),(0,[z1,z916,z3,z8,z5,z6]),(0,[z221,z303,z3,z8,z5,z6]),(0,[z193,z1,z2,z3,z8,z613])],[(0,[z691,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z917,z5,z6]),(0,[z1,z35,z3,z8,z48,z60]),(0,[z1,z2,z3,z54,z5,z6]),(0,[z1,z2,z3,z8,z5,z918])],[(0,[z1,z2,z3,z919,z5,z6]),(0,[z1,z2,z3,z8,z920,z6]),(0,[z1,z2,z3,z8,z5,z921]),(0,[z1,z2,z3,z8,z922,z6]),(0,[z1,z98,z3,z104,z99,z6]),(0,[z81,z1,z2,z3,z11,z45])],[(0,[z1,z2,z3,z8,z343,z6]),(0,[z1,z2,z299,z8,z5,z183]),(0,[z1,z2,z3,z8,z6,z923]),(0,[z1,z2,z3,z8,z5,z924]),(0,[z1,z2,z3,z8,z48,z925])],[(0,[z0,z46,z3,z8,z5,z42]),(0,[z93,z394,z103,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z926]),(0,[z1,z2,z3,z8,z321,z60])],[(0,[z927,z1,z2,z3,z8,z5]),(0,[z7,z2,z3,z8,z11,z9]),(0,[z1,z35,z103,z8,z5,z60]),(0,[z1,z2,z3,z8,z147,z60]),(0,[z1,z3,z8,z928,z48,z6]),(0,[z1,z2,z3,z929,z48,z6])],[(0,[z1,z224,z3,z411,z5,z6]),(0,[z30,z1,z3,z8,z48,z60]),(0,[z394,z2,z3,z8,z5,z250]),(0,[z1,z2,z3,z8,z930,z6]),(0,[z1,z2,z3,z163,z8,z42]),(0,[z1,z931,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z314,z183]),(0,[z32,z2,z3,z33,z11,z6]),(0,[z1,z3,z8,z562,z48,z6]),(0,[z1,z2,z3,z73,z80,z6]),(0,[z1,z2,z3,z932,z5,z60]),(0,[z1,z200,z2,z5,z739,z6])],[],[(0,[z694,z46,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z346,z240]),(0,[z1,z2,z3,z8,z11,z52])],[(0,[z1,z2,z3,z8,z172,z20]),(0,[z93,z1,z103,z8,z5,z250]),(0,[z1,z2,z933,z8,z5,z6]),(0,[z1,z3,z8,z934,z48,z6]),(0,[z1,z417,z3,z8,z5,z42]),(0,[z396,z1,z2,z3,z8,z17])],[(0,[z935,z2,z3,z8,z5,z6]),(0,[z53,z1,z3,z8,z48,z60]),(0,[z1,z2,z3,z936,z5,z60]),(0,[z1,z2,z3,z169,z124,z6]),(0,[z1,z500,z2,z158,z8,z6])]],
   [[(0,[z1,z2,z937,z3,z5,z6])],[(0,[z1,z386,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z938,z6]),(0,[z371,z2,z3,z8,z290,z6]),(0,[z371,z2,z3,z8,z5,z138]),(0,[z1,z2,z3,z939,z5,z6]),(0,[z1,z511,z3,z8,z395,z6])],[(0,[z1,z2,z299,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z940]),(0,[z1,z2,z3,z405,z5,z327]),(0,[z1,z303,z3,z8,z321,z6])],[(0,[z1,z224,z3,z8,z5,z60]),(0,[z1,z2,z3,z411,z5,z42]),(0,[z2,z714,z21,z8,z5,z6]),(0,[z1,z2,z3,z8,z99,z6]),(0,[z1,z2,z376,z8,z290,z6]),(0,[z1,z2,z376,z8,z5,z138])],[(0,[z71,z2,z21,z8,z5,z88]),(0,[z1,z2,z941,z3,z8,z6]),(0,[z1,z2,z3,z8,z48,z517]),(0,[z1,z2,z942,z8,z5,z6]),(0,[z1,z3,z8,z5,z48,z64]),(0,[z1,z3,z8,z5,z42,z269]),(0,[z70,z2,z3,z8,z321,z6])],[(0,[z1,z3,z8,z5,z928,z6]),(0,[z1,z2,z3,z943,z5,z6]),(0,[z944,z1,z2,z3,z8,z5]),(0,[z945,z2,z3,z8,z5,z42]),(0,[z221,z2,z3,z356,z5,z6])],[(0,[z545,z1,z103,z8,z5,z6]),(0,[z1,z2,z3,z946,z5,z6]),(0,[z1,z511,z3,z8,z5,z118]),(0,[z1,z2,z3,z8,z5,z947])],[(0,[z142,z2,z3,z208,z5,z6]),(0,[z1,z2,z3,z8,z5,z948]),(0,[z1,z2,z3,z8,z5,z949])],[(0,[z575,z2,z3,z217,z5,z6]),(0,[z1,z2,z3,z8,z950,z6]),(0,[z85,z1,z3,z251,z5,z60]),(0,[z1,z2,z3,z506,z158,z6]),(0,[z951,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z8,z952,z6]),(0,[z1,z2,z3,z8,z953,z6])],[(0,[z1,z391,z3,z8,z48,z60])],[(0,[z2,z753,z3,z8,z5,z6]),(0,[z1,z2,z3,z954,z5,z6])],[(0,[z1,z2,z3,z8,z955,z6]),(0,[z1,z2,z3,z8,z5,z925]),(0,[z85,z1,z3,z8,z48,z60]),(0,[z1,z114,z3,z8,z11,z6]),(0,[z1,z956,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z767])],[(0,[z1,z2,z3,z8,z6,z957]),(0,[z1,z2,z3,z8,z5,z812]),(0,[z958,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z959,z8,z6]),(0,[z1,z2,z3,z8,z960,z6])],[(0,[z1,z46,z3,z8,z48,z60]),(0,[z1,z2,z3,z929,z5,z6]),(0,[z1,z2,z3,z961,z5,z6]),(0,[z1,z300,z3,z242,z5,z6]),(0,[z1,z2,z3,z506,z48,z42])],[(0,[z1,z14,z3,z8,z5,z108]),(0,[z1,z2,z3,z506,z147,z6])],[(0,[z1,z2,z3,z8,z5,z962]),(0,[z1,z2,z129,z8,z290,z6]),(0,[z1,z2,z129,z8,z5,z138])]],
   [[(0,[z1,z21,z103,z8,z5,z60]),(0,[z497,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z42,z963]),(0,[z1,z2,z3,z8,z964,z6])],[(0,[z394,z2,z3,z8,z5,z60]),(0,[z193,z1,z2,z3,z8,z539])],[(0,[z1,z2,z3,z8,z965,z6]),(0,[z101,z2,z3,z33,z5,z6]),(0,[z662,z2,z3,z8,z68,z6]),(0,[z2,z3,z8,z48,z873,z6]),(0,[z1,z2,z3,z966,z48,z6]),(0,[z1,z2,z3,z231,z336,z6])],[(0,[z1,z2,z3,z8,z390,z42]),(0,[z481,z1,z3,z8,z48,z6]),(0,[z967,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z968,z8,z60]),(0,[z1,z2,z3,z356,z321,z6])],[(0,[z1,z2,z3,z8,z5,z969]),(0,[z94,z2,z3,z8,z48,z6]),(0,[z970,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z48,z6,z876])],[(0,[z1,z2,z3,z971,z5,z6]),(0,[z1,z114,z3,z8,z5,z108]),(0,[z1,z2,z3,z8,z48,z468])],[(0,[z1,z2,z3,z8,z5,z972]),(0,[z1,z2,z35,z383,z5,z6]),(0,[z1,z476,z3,z8,z5,z60]),(0,[z1,z303,z3,z8,z5,z42]),(0,[z1,z2,z3,z8,z973,z6]),(0,[z1,z2,z3,z8,z5,z974])],[(0,[z1,z2,z3,z208,z5,z42]),(0,[z161,z1,z3,z251,z5,z6]),(0,[z91,z1,z2,z3,z506,z6]),(0,[z81,z1,z2,z3,z5,z281]),(0,[z1,z2,z3,z8,z975,z6]),(0,[z1,z2,z937,z3,z80,z6]),(0,[z81,z397,z2,z3,z5,z45])],[(0,[z1,z2,z976,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z977]),(0,[z1,z2,z3,z8,z5,z517]),(0,[z94,z2,z103,z8,z5,z6]),(0,[z394,z2,z3,z8,z390,z6]),(0,[z978,z2,z3,z8,z5,z6]),(0,[z1,z10,z3,z8,z5,z826]),(0,[z70,z2,z3,z8,z5,z42])],[(0,[z1,z2,z3,z8,z5,z979]),(0,[z1,z2,z3,z8,z980,z6]),(1,[z2,z3,z92,z5,z118]),(0,[z1,z2,z3,z169,z5,z60]),(0,[z1,z2,z3,z8,z5,z981])],[(0,[z1,z2,z3,z8,z314,z6]),(0,[z1,z2,z3,z8,z982,z6])],[(0,[z371,z2,z376,z8,z5,z6])],[(0,[z1,z2,z3,z983,z5,z6]),(0,[z2,z3,z8,z217,z5,z179]),(0,[z30,z2,z3,z217,z48,z6]),(0,[z1,z24,z2,z5,z107,z6]),(0,[z1,z2,z3,z8,z146,z108]),(0,[z1,z19,z3,z8,z11,z6]),(0,[z1,z320,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z984,z6])],[(0,[z1,z2,z3,z8,z11,z183]),(0,[z1,z96,z103,z8,z5,z60]),(0,[z985,z2,z3,z8,z5,z6]),(0,[z85,z1,z3,z661,z5,z6]),(0,[z1,z2,z3,z8,z5,z986])],[(0,[z1,z2,z3,z8,z5,z987]),(0,[z206,z2,z96,z8,z5,z6])],[(0,[z1,z2,z3,z236,z5,z60])]],
   [[(0,[z1,z2,z3,z8,z988,z6]),(0,[z1,z2,z3,z311,z8,z60]),(0,[z1,z2,z3,z8,z989,z6]),(0,[z1,z182,z3,z8,z48,z60]),(0,[z1,z3,z8,z5,z267,z60])],[(0,[z1,z2,z3,z506,z5,z42]),(0,[z1,z2,z3,z990,z8,z6])],[(0,[z1,z2,z3,z991,z5,z6]),(0,[z1,z2,z3,z8,z5,z992]),(0,[z1,z2,z3,z814,z5,z6])],[(0,[z642,z1,z2,z3,z5,z45]),(0,[z1,z2,z3,z205,z11,z6]),(0,[z2,z3,z92,z5,z6,z118]),(0,[z350,z1,z3,z8,z48,z60]),(0,[z1,z3,z8,z470,z48,z6])],[(0,[z1,z2,z3,z49,z48,z6])],[(0,[z1,z10,z3,z8,z11,z60]),(0,[z1,z2,z3,z8,z993,z6])],[(0,[z1,z2,z3,z8,z994,z6]),(0,[z1,z2,z3,z966,z5,z6]),(0,[z1,z493,z3,z104,z5,z6])],[(0,[z519,z2,z3,z8,z5,z118]),(0,[z350,z1,z103,z8,z5,z60]),(0,[z967,z2,z3,z8,z5,z6]),(0,[z371,z2,z129,z8,z5,z6]),(0,[z1,z2,z3,z8,z48,z64]),(0,[z1,z3,z8,z5,z227,z60]),(0,[z1,z2,z3,z356,z5,z42])],[(0,[z546,z2,z21,z8,z5,z6]),(0,[z93,z1,z995,z8,z5,z6]),(0,[z1,z2,z3,z8,z928,z6])],[(0,[z1,z2,z3,z8,z5,z468]),(0,[z1,z450,z2,z8,z585,z6]),(0,[z1,z3,z8,z87,z48,z6]),(0,[z1,z2,z3,z818,z5,z6]),(0,[z1,z2,z3,z8,z626,z42]),(0,[z1,z2,z35,z36,z163,z6]),(0,[z1,z2,z3,z8,z5,z996])],[(0,[z1,z997,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z998,z6]),(0,[z1,z3,z21,z8,z48,z60]),(0,[z1,z2,z3,z999,z5,z6]),(0,[z325,z1,z3,z8,z48,z6])],[(0,[z1,z300,z3,z8,z5,z60]),(0,[z1,z302,z3,z8,z5,z60]),(0,[z69,z2,z3,z8,z5,z42]),(0,[z1,z3,z8,z251,z48,z60]),(0,[z1,z2,z3,z8,z261,z42])],[(0,[z1,z2,z3,z8,z5,z1000])],[(0,[z1,z2,z3,z8,z1001,z6]),(0,[z1,z2,z3,z8,z11,z88]),(0,[z1,z2,z3,z570,z48,z6]),(0,[z1,z2,z3,z8,z395,z135])],[(0,[z1,z3,z103,z8,z5,z250]),(0,[z1002,z2,z3,z8,z5,z6]),(0,[z1,z220,z3,z8,z5,z60]),(0,[z1,z2,z36,z5,z739,z6])],[(0,[z0,z46,z3,z4,z5,z6]),(0,[z1,z753,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1003]),(0,[z1,z2,z3,z92,z48,z6]),(0,[z1,z320,z56,z8,z5,z6]),(0,[z1,z2,z3,z8,z1004,z6])]],
   [[(0,[z1,z300,z3,z8,z1005,z6]),(0,[z30,z2,z3,z217,z5,z6]),(0,[z1,z2,z3,z8,z5,z1006]),(0,[z1,z2,z3,z506,z135,z6]),(0,[z1,z2,z3,z8,z51,z42])],[(0,[z1,z2,z352,z8,z314,z6]),(0,[z53,z1,z2,z8,z48,z37]),(0,[z1,z258,z3,z8,z5,z60])],[(0,[z1,z97,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z1007,z6]),(0,[z1,z2,z3,z8,z48,z108]),(0,[z1,z2,z3,z8,z11,z138]),(0,[z1,z194,z2,z182,z3,z6])],[(0,[z1,z2,z3,z8,z5,z1008]),(0,[z1,z2,z3,z8,z1009,z6]),(0,[z1,z2,z3,z8,z5,z1010]),(0,[z1,z3,z8,z48,z6,z447]),(0,[z1,z3,z8,z330,z5,z60])],[(0,[z1,z2,z3,z8,z11,z257]),(0,[z1011,z2,z3,z8,z5,z60])],[(0,[z1,z2,z3,z8,z5,z1012]),(0,[z1,z3,z8,z5,z42,z812]),(0,[z1,z303,z3,z8,z5,z16])],[(0,[z1,z2,z3,z8,z5,z1013]),(0,[z1,z2,z3,z8,z172,z60]),(0,[z2,z300,z21,z8,z5,z6]),(0,[z1,z3,z104,z8,z48,z60])],[],[(0,[z1,z2,z3,z49,z5,z6]),(0,[z1,z3,z8,z17,z48,z60]),(0,[z1,z2,z3,z8,z850,z125])],[(0,[z1,z300,z96,z8,z5,z6]),(0,[z2,z3,z8,z750,z5,z6]),(0,[z1,z2,z1014,z8,z5,z6])],[(0,[z601,z1,z3,z8,z5,z60])],[(0,[z1,z2,z3,z8,z5,z64]),(0,[z1015,z1,z2,z3,z8,z5]),(0,[z53,z1,z2,z8,z252,z37])],[(0,[z1,z2,z3,z8,z11,z6]),(0,[z535,z2,z3,z217,z5,z6]),(0,[z1,z2,z3,z8,z1016,z6])],[(0,[z1017,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1018]),(0,[z1,z3,z8,z48,z135,z60]),(0,[z1,z3,z8,z626,z48,z6]),(0,[z396,z1,z887,z3,z8,z5]),(0,[z1,z2,z3,z8,z6,z77])],[(0,[z1,z2,z522,z8,z124,z6])],[(0,[z1,z2,z3,z1019,z172,z6]),(0,[z1,z2,z3,z1020,z48,z6]),(0,[z1,z1021,z3,z8,z5,z6]),(0,[z1,z716,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z1022])],[(0,[z1,z2,z3,z8,z6,z1023]),(0,[z1,z3,z8,z48,z6,z477]),(0,[z1,z2,z3,z570,z5,z6])],[(0,[z1,z2,z3,z205,z5,z517]),(0,[z7,z1,z3,z8,z48,z60]),(0,[z1,z2,z3,z8,z1024,z6])],[(0,[z1,z2,z3,z8,z5,z1025]),(0,[z1,z2,z3,z92,z5,z6]),(0,[z221,z114,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1026,z6]),(0,[z1,z2,z3,z8,z6,z1027])],[(0,[z1,z3,z8,z48,z6,z60]),(0,[z1,z2,z140,z8,z152,z6])],[(0,[z1,z2,z3,z1028,z172,z6]),(0,[z1,z2,z3,z242,z5,z60]),(0,[z1,z2,z549,z8,z5,z16]),(0,[z53,z1,z2,z8,z5,z37])],[(0,[z1,z2,z3,z8,z5,z108]),(0,[z1,z2,z3,z1029,z8,z6]),(0,[z1,z424,z3,z8,z5,z60])],[(0,[z46,z21,z103,z8,z5,z6]),(0,[z1,z2,z3,z8,z1030,z6]),(0,[z1,z3,z8,z48,z171,z60]),(0,[z1,z2,z3,z1031,z5,z60])],[(0,[z305,z1,z3,z73,z48,z6]),(0,[z263,z2,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z77,z60])],[(0,[z142,z126,z3,z8,z11,z6]),(0,[z1,z3,z8,z5,z1032,z6]),(0,[z1,z2,z3,z80,z625,z6]),(0,[z1,z2,z3,z1033,z5,z6]),(0,[z1,z2,z3,z8,z11,z327]),(0,[z1,z2,z3,z8,z48,z201]),(0,[z1,z2,z5,z739,z107,z6])],[(0,[z2,z46,z3,z208,z5,z6]),(0,[z1,z353,z3,z8,z5,z60]),(0,[z1,z2,z3,z1034,z5,z6]),(0,[z1,z98,z3,z104,z387,z6]),(0,[z1,z14,z3,z8,z48,z42])],[(0,[z1,z2,z3,z8,z5,z1035]),(0,[z1,z2,z3,z8,z1036,z6]),(0,[z1,z453,z3,z8,z5,z60])],[(0,[z91,z2,z3,z8,z770,z6]),(0,[z1,z200,z2,z5,z107,z6])],[(0,[z1,z2,z3,z8,z5,z801]),(0,[z235,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z48,z573]),(0,[z1,z2,z35,z36,z5,z60])],[(0,[z1,z2,z3,z8,z5,z1037]),(0,[z1,z2,z3,z506,z241,z6])],[(0,[z0,z46,z3,z8,z5,z60]),(1,[z1,z2,z8,z772,z6])]],
   [[(0,[z1,z2,z3,z1038,z5,z6]),(0,[z1,z98,z3,z104,z5,z201]),(0,[z865,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z1039,z6]),(0,[z1,z3,z8,z48,z416,z60]),(0,[z1,z2,z3,z163,z8,z60]),(0,[z1,z114,z3,z8,z321,z6])],[(0,[z1,z2,z3,z8,z5,z1040]),(0,[z1,z3,z8,z5,z412,z60]),(0,[z47,z2,z3,z8,z11,z118]),(0,[z47,z1,z3,z8,z48,z60]),(1,[z1,z3,z8,z346,z60]),(0,[z287,z1,z2,z3,z5,z360])],[(0,[z1,z2,z352,z8,z11,z6]),(0,[z1,z2,z3,z8,z390,z250]),(0,[z1,z2,z3,z1020,z5,z6]),(0,[z1,z2,z3,z8,z11,z240])],[(0,[z30,z2,z3,z311,z217,z6]),(0,[z1,z2,z3,z8,z11,z143]),(0,[z93,z1,z3,z8,z48,z60]),(0,[z1,z2,z182,z129,z5,z6]),(0,[z1,z3,z8,z124,z48,z60]),(0,[z397,z2,z3,z8,z5,z60])],[(0,[z2,z3,z33,z750,z5,z6]),(0,[z32,z2,z3,z33,z5,z42]),(0,[z1,z2,z3,z8,z5,z1041]),(0,[z1,z2,z3,z1042,z8,z42])],[(0,[z123,z1,z103,z8,z5,z6]),(0,[z1043,z2,z3,z8,z5,z6])],[(0,[z0,z46,z3,z8,z5,z197]),(0,[z32,z1,z3,z8,z48,z60]),(0,[z1,z2,z1044,z8,z5,z6]),(0,[z1,z3,z8,z159,z48,z60]),(0,[z1,z2,z3,z1045,z5,z6]),(0,[z1,z2,z3,z120,z11,z6]),(0,[z1,z2,z3,z8,z387,z6]),(0,[z1,z2,z3,z778,z5,z42]),(0,[z1,z2,z3,z8,z5,z859])],[(0,[z93,z1,z103,z8,z5,z60]),(0,[z1,z3,z995,z8,z5,z6]),(0,[z776,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z506,z267,z6]),(0,[z1,z18,z3,z8,z48,z6])],[(0,[z1,z2,z299,z8,z5,z6]),(0,[z1,z2,z1046,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1047]),(0,[z47,z2,z3,z92,z5,z118]),(0,[z1,z2,z3,z8,z1048,z6]),(0,[z587,z1,z2,z3,z5,z281]),(0,[z221,z2,z3,z8,z5,z37])],[(0,[z1,z2,z1049,z8,z5,z6]),(0,[z1,z2,z3,z411,z5,z60]),(0,[z1,z2,z3,z8,z155,z79]),(0,[z1,z2,z3,z8,z11,z210]),(0,[z1,z3,z8,z48,z60,z199])],[(0,[z1,z2,z299,z8,z408,z6]),(0,[z1,z300,z21,z8,z5,z6]),(0,[z1,z2,z3,z8,z48,z31]),(0,[z1,z2,z3,z8,z5,z1050]),(0,[z69,z2,z3,z8,z147,z6]),(0,[z1,z3,z8,z48,z241,z60])],[(0,[z1,z2,z3,z8,z5,z1051]),(0,[z1,z96,z3,z8,z48,z60]),(0,[z1,z697,z3,z8,z48,z6])],[(0,[z0,z753,z3,z8,z5,z6]),(0,[z1,z126,z3,z8,z48,z60]),(0,[z1,z583,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z201]),(0,[z1,z2,z3,z8,z5,z1052]),(0,[z1,z2,z3,z1053,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1054]),(0,[z1,z3,z33,z8,z48,z60]),(0,[z1,z2,z3,z405,z315,z6]),(0,[z1,z2,z3,z506,z124,z6]),(0,[z1,z14,z3,z8,z5,z42]),(0,[z1,z2,z716,z3,z8,z5]),(0,[z1,z194,z2,z3,z6,z102])],[(0,[z1,z2,z3,z8,z1055,z6]),(0,[z93,z1,z103,z8,z390,z6])]],
   [[(0,[z221,z2,z3,z8,z48,z6]),(0,[z1056,z2,z3,z8,z5,z6])],[(0,[z1057,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z573]),(0,[z305,z1,z3,z8,z48,z6]),(0,[z1,z511,z3,z8,z48,z6])],[(0,[z1,z2,z3,z8,z5,z1058]),(0,[z1059,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z80,z387,z6]),(0,[z1,z596,z3,z8,z48,z6]),(0,[z1,z548,z3,z8,z5,z60])],[(0,[z1,z2,z3,z8,z1060,z6]),(0,[z94,z2,z3,z405,z5,z6]),(0,[z1,z3,z8,z48,z6,z191]),(0,[z1,z2,z8,z772,z5,z6]),(0,[z1,z2,z3,z8,z17,z321])],[(0,[z1,z2,z3,z8,z5,z1061]),(0,[z1,z2,z3,z8,z1062,z6]),(0,[z1,z2,z3,z917,z346,z6]),(0,[z1,z2,z3,z506,z48,z60]),(0,[z1063,z2,z3,z8,z5,z6])],[(0,[z1,z300,z3,z411,z5,z6]),(0,[z1,z224,z3,z8,z155,z6]),(0,[z1,z3,z8,z48,z267,z60]),(0,[z1,z114,z3,z8,z5,z42]),(0,[z1,z303,z3,z8,z1064,z6]),(0,[z1,z2,z3,z8,z1065,z6])],[(0,[z1,z2,z3,z8,z5,z1066]),(0,[z2,z3,z217,z5,z118,z45]),(0,[z1,z2,z3,z1067,z5,z6]),(0,[z1,z2,z3,z8,z315,z6]),(0,[z1,z2,z3,z8,z233,z6]),(0,[z1,z2,z3,z73,z11,z6])],[(0,[z1,z151,z3,z8,z928,z6])],[(0,[z1,z2,z3,z1068,z5,z6]),(0,[z164,z1,z3,z8,z11,z60]),(0,[z1,z2,z3,z8,z5,z1069])],[(0,[z1,z200,z3,z8,z48,z60]),(0,[z1,z2,z3,z73,z48,z42]),(0,[z350,z1,z2,z8,z5,z37])],[(0,[z1,z2,z3,z8,z390,z60]),(0,[z1070,z2,z3,z8,z5,z6]),(0,[z1,z2,z140,z8,z52,z124]),(0,[z221,z2,z3,z8,z252,z6]),(0,[z1,z194,z2,z937,z3,z6])],[(0,[z94,z2,z3,z8,z5,z6]),(0,[z91,z2,z3,z8,z68,z6])],[(0,[z7,z2,z3,z8,z5,z705]),(0,[z1,z2,z3,z8,z146,z42]),(0,[z1,z2,z937,z3,z279,z6]),(0,[z1,z2,z3,z8,z5,z1071])],[(0,[z1,z2,z1072,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1073]),(0,[z1,z303,z3,z8,z5,z60]),(0,[z292,z2,z3,z8,z5,z471]),(0,[z1,z2,z15,z8,z5,z859])],[(0,[z1,z2,z3,z8,z1074,z6]),(0,[z1,z2,z3,z8,z155,z42]),(0,[z1,z2,z3,z8,z48,z79]),(0,[z1,z2,z3,z8,z1075,z6]),(0,[z1,z2,z140,z8,z124,z6]),(0,[z1,z2,z3,z8,z5,z1076]),(0,[z1,z511,z3,z8,z17,z6])],[(0,[z1,z2,z3,z8,z5,z31]),(0,[z70,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z80,z621,z6])]],
   [[(0,[z1,z2,z3,z8,z1077,z6]),(0,[z1,z2,z3,z8,z1078,z6]),(0,[z1,z2,z3,z8,z1079,z6]),(0,[z1,z2,z3,z8,z5,z1080]),(0,[z1,z2,z35,z5,z739,z6]),(0,[z1,z2,z3,z1081,z5,z6])],[(0,[z1,z2,z3,z8,z1082,z6]),(0,[z1,z2,z3,z932,z48,z6]),(0,[z1,z2,z3,z8,z11,z227]),(0,[z1,z2,z3,z8,z1083,z60]),(0,[z1,z2,z35,z36,z51,z6]),(0,[z1,z114,z3,z8,z1084,z6]),(0,[z1,z2,z3,z1085,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1086]),(0,[z1,z2,z3,z8,z5,z1087]),(0,[z1,z2,z3,z8,z1088,z6]),(0,[z1,z14,z3,z8,z348,z42]),(0,[z1,z1089,z3,z8,z5,z6])],[(0,[z1,z300,z3,z8,z5,z1090]),(0,[z1,z2,z3,z8,z315,z327]),(0,[z1,z1091,z3,z8,z5,z6])],[(0,[z221,z2,z3,z8,z5,z6]),(0,[z1,z3,z103,z8,z48,z60]),(0,[z1,z2,z15,z8,z48,z16])],[(0,[z1,z2,z3,z8,z1092,z6]),(0,[z1,z2,z3,z8,z1093,z6]),(0,[z1,z511,z3,z8,z5,z6])],[(0,[z1,z1094,z2,z3,z92,z6]),(0,[z1,z2,z3,z8,z11,z845]),(0,[z1,z19,z3,z8,z5,z42]),(0,[z413,z1,z2,z3,z5,z45])],[(0,[z1,z2,z3,z405,z11,z6]),(0,[z1,z3,z73,z8,z48,z60]),(0,[z1,z2,z3,z506,z585,z6]),(0,[z1,z2,z3,z1095,z5,z6])],[(0,[z94,z2,z3,z8,z5,z327]),(0,[z1,z2,z3,z506,z5,z60])],[(0,[z1,z224,z3,z8,z48,z6]),(0,[z662,z1,z3,z8,z48,z60]),(0,[z1,z3,z73,z48,z6,z60]),(0,[z1,z3,z8,z11,z928,z6]),(0,[z1,z2,z3,z8,z5,z1096]),(0,[z70,z303,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1097]),(0,[z1,z151,z3,z8,z5,z64]),(0,[z1,z2,z3,z80,z336,z6]),(0,[z2,z3,z8,z5,z42,z745])],[(0,[z1,z2,z3,z8,z48,z179]),(0,[z1,z2,z3,z8,z1098,z6]),(0,[z1,z2,z3,z8,z5,z1099]),(0,[z1,z151,z3,z8,z11,z6]),(0,[z1,z194,z2,z3,z73,z6])],[(0,[z193,z1,z2,z3,z8,z133])],[(0,[z1,z364,z3,z8,z48,z6]),(0,[z1,z2,z3,z205,z5,z42]),(0,[z1,z3,z8,z5,z42,z695]),(0,[z193,z1,z2,z3,z8,z137]),(0,[z1,z3,z506,z11,z48,z6])],[(0,[z1,z2,z3,z8,z5,z1100]),(0,[z85,z1,z3,z251,z48,z6]),(0,[z1,z2,z3,z356,z5,z60]),(0,[z1,z322,z3,z8,z5,z42])],[(0,[z1,z2,z3,z8,z1101,z6]),(0,[z7,z2,z3,z8,z5,z401])]],
   [[(0,[z71,z1,z3,z8,z48,z60]),(0,[z350,z1,z2,z8,z5,z145])],[(0,[z1,z2,z3,z8,z1102,z6]),(0,[z1,z2,z3,z8,z1103,z6]),(0,[z385,z2,z21,z8,z5,z6]),(0,[z629,z2,z3,z217,z5,z6]),(0,[z25,z1,z2,z3,z506,z6]),(0,[z1,z2,z3,z73,z387,z6]),(0,[z1,z2,z3,z1104,z48,z6])],[(0,[z1,z2,z3,z8,z5,z79]),(0,[z1,z2,z3,z8,z48,z42]),(0,[z1,z3,z8,z48,z60,z60]),(0,[z1,z2,z3,z8,z321,z6])],[(0,[z1,z2,z3,z1105,z5,z6]),(0,[z1,z2,z3,z8,z147,z6])],[(0,[z1,z2,z652,z36,z5,z6]),(0,[z119,z1,z3,z8,z48,z60]),(1,[z1,z511,z3,z8,z125])],[(0,[z1,z2,z3,z932,z5,z6]),(0,[z1,z2,z3,z8,z1106,z60])],[(0,[z1,z2,z3,z4,z5,z60]),(0,[z1,z2,z3,z8,z5,z1107]),(0,[z1,z2,z3,z8,z5,z1108])],[(0,[z394,z2,z3,z8,z48,z6])],[(0,[z1,z2,z3,z49,z5,z327]),(0,[z1,z3,z103,z8,z5,z60]),(0,[z1,z2,z15,z8,z5,z16])],[(0,[z1,z2,z3,z8,z5,z1109]),(0,[z1,z2,z3,z1110,z5,z6]),(0,[z1,z2,z3,z8,z5,z1111]),(0,[z1,z458,z3,z8,z5,z60]),(0,[z1,z98,z3,z104,z5,z42]),(0,[z1,z2,z3,z936,z5,z6]),(0,[z1,z2,z3,z8,z1112,z6])],[(0,[z22,z2,z3,z8,z5,z118]),(0,[z1,z244,z2,z3,z8,z42]),(0,[z1,z2,z1113,z8,z5,z6]),(0,[z70,z2,z3,z356,z5,z6])],[(0,[z1,z2,z3,z8,z819,z6]),(0,[z1,z3,z8,z217,z48,z60]),(0,[z1,z2,z182,z3,z387,z6]),(0,[z1114,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1115,z5,z6]),(0,[z1,z2,z3,z8,z252,z42]),(0,[z81,z1,z2,z3,z77,z45])],[(0,[z1,z224,z3,z8,z5,z6]),(0,[z1,z300,z3,z8,z155,z6]),(0,[z371,z2,z3,z8,z11,z6]),(0,[z1,z2,z3,z8,z17,z253]),(0,[z1116,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z197]),(0,[z657,z2,z3,z217,z5,z6]),(0,[z1,z2,z3,z80,z147,z6]),(0,[z193,z1,z2,z3,z8,z199])],[(0,[z1,z2,z3,z8,z5,z179]),(0,[z1,z2,z376,z8,z11,z6]),(0,[z1,z2,z3,z169,z48,z6]),(0,[z1,z544,z3,z8,z5,z42]),(0,[z1,z2,z3,z8,z1117,z6])]],
   [[(0,[z1,z2,z3,z1118,z5,z6]),(0,[z1,z2,z3,z8,z1119,z6])],[(0,[z1,z2,z3,z1120,z5,z6]),(0,[z1,z2,z3,z8,z5,z1121]),(0,[z1122,z2,z3,z8,z5,z60])],[(0,[z1,z2,z3,z8,z1123,z6]),(0,[z123,z1,z3,z251,z5,z6]),(0,[z1,z2,z3,z8,z1124,z6]),(0,[z164,z1,z3,z8,z233,z60]),(0,[z1,z2,z3,z8,z1125,z6]),(0,[z1,z2,z3,z8,z5,z1126])],[(0,[z1,z2,z1127,z8,z5,z6]),(0,[z1,z1128,z3,z8,z5,z6]),(0,[z1,z420,z3,z104,z5,z6]),(0,[z1,z2,z3,z8,z5,z737]),(0,[z1,z2,z3,z8,z1129,z6])],[(0,[z1,z2,z3,z8,z5,z1130]),(0,[z2,z3,z21,z8,z5,z88]),(0,[z1,z2,z3,z1131,z5,z6]),(0,[z482,z2,z3,z33,z5,z6]),(0,[z1,z3,z8,z5,z1080,z60])],[(0,[z71,z2,z21,z8,z11,z6]),(0,[z1,z2,z3,z1132,z5,z6]),(0,[z1,z2,z3,z236,z48,z6]),(1,[z2,z3,z8,z5,z737]),(0,[z1,z3,z8,z5,z554,z60]),(0,[z1,z2,z3,z1104,z5,z6]),(0,[z1,z3,z8,z48,z60,z382]),(0,[z1,z2,z3,z8,z5,z1133])],[(0,[z1,z2,z3,z8,z5,z42]),(0,[z1,z450,z3,z8,z48,z60]),(0,[z1,z3,z8,z48,z225,z60]),(0,[z1134,z2,z3,z8,z5,z6]),(0,[z1,z2,z15,z8,z5,z294])],[(0,[z1,z3,z414,z8,z5,z60])],[(0,[z1,z2,z3,z8,z1135,z6]),(0,[z1,z2,z3,z8,z5,z1136]),(0,[z590,z1,z2,z3,z5,z45]),(0,[z1,z2,z3,z8,z1137,z6])],[(0,[z142,z1,z3,z8,z48,z60]),(0,[z1,z2,z3,z8,z5,z1138]),(0,[z599,z1,z2,z3,z8,z125])],[(0,[z1,z2,z3,z8,z1139,z6]),(0,[z1140,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1141,z6]),(0,[z1,z2,z3,z8,z1142,z6]),(0,[z1,z2,z3,z8,z17,z135])],[(0,[z394,z2,z3,z8,z5,z6]),(0,[z1,z2,z129,z8,z11,z6]),(0,[z1,z2,z3,z1143,z48,z6]),(0,[z193,z1,z3,z8,z48,z60]),(0,[z1,z304,z3,z8,z11,z6]),(0,[z1144,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z1145,z6]),(0,[z1,z2,z3,z311,z36,z6])],[(0,[z142,z2,z352,z8,z5,z6]),(0,[z1,z2,z3,z1146,z5,z6]),(0,[z2,z46,z352,z8,z5,z6]),(0,[z0,z46,z3,z208,z5,z6]),(0,[z1,z194,z2,z3,z8,z517]),(0,[z1,z2,z3,z8,z5,z1147]),(0,[z1,z2,z3,z968,z8,z6]),(0,[z599,z1,z2,z3,z506,z6]),(0,[z1,z3,z567,z8,z5,z60]),(0,[z1,z2,z3,z8,z781,z42])],[(0,[z1,z2,z3,z8,z1148,z6]),(0,[z325,z1,z2,z3,z8,z125]),(0,[z1,z2,z3,z1149,z5,z6])],[(0,[z362,z2,z3,z8,z159,z6]),(0,[z1,z2,z3,z1150,z48,z6]),(0,[z1,z2,z15,z8,z5,z225]),(1,[z1,z2,z937,z3,z6])]],
   [[(1,[z300,z21,z8,z5,z6]),(0,[z1,z2,z3,z8,z1151,z6]),(0,[z1,z2,z158,z8,z772,z6])],[(0,[z1,z2,z3,z8,z48,z20]),(0,[z1,z300,z3,z8,z48,z6]),(0,[z1,z2,z3,z1152,z5,z6]),(0,[z1,z2,z714,z8,z5,z6]),(0,[z1,z2,z3,z1153,z8,z6]),(0,[z1,z2,z3,z8,z5,z1154]),(0,[z1,z1155,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1156]),(0,[z1,z513,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z147,z210]),(0,[z1,z14,z3,z8,z48,z60]),(0,[z1,z2,z3,z1157,z8,z6])],[(0,[z1,z3,z8,z5,z261,z60]),(0,[z263,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z8,z1084,z6])],[(0,[z173,z2,z425,z8,z5,z6]),(0,[z1,z2,z3,z169,z5,z6])],[(0,[z1,z244,z2,z3,z205,z6])],[(0,[z1,z3,z8,z585,z48,z60])],[(0,[z1,z2,z3,z8,z283,z79]),(0,[z1,z2,z3,z89,z5,z631])],[(0,[z1,z2,z3,z242,z155,z6]),(0,[z91,z2,z3,z650,z8,z6]),(0,[z1,z258,z3,z8,z48,z6])],[(0,[z1,z2,z3,z792,z5,z6]),(0,[z116,z1,z3,z8,z5,z60]),(0,[z1,z2,z3,z1158,z5,z6])],[(0,[z1,z2,z3,z236,z5,z6]),(0,[z1,z2,z3,z8,z5,z1159]),(0,[z1,z2,z8,z5,z739,z6]),(0,[z1,z2,z8,z5,z16,z859])],[(0,[z1,z2,z3,z311,z8,z6]),(0,[z1,z14,z3,z8,z934,z6]),(0,[z1,z2,z3,z8,z348,z42])],[(0,[z1,z2,z3,z1160,z48,z6])],[(0,[z1,z2,z1161,z8,z5,z6]),(0,[z32,z2,z3,z33,z5,z60]),(0,[z396,z1,z194,z2,z3,z8])],[(0,[z1,z2,z352,z8,z5,z42]),(0,[z1,z2,z3,z8,z1162,z6]),(0,[z1,z2,z522,z8,z554,z6])],[(0,[z1,z27,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z245,z135]),(0,[z1,z2,z3,z134,z8,z42])],[(0,[z1,z2,z3,z1143,z5,z6]),(0,[z1,z2,z3,z8,z1005,z6]),(0,[z1,z151,z3,z8,z5,z1080]),(0,[z1,z3,z8,z5,z60,z442])]],
   [[(0,[z85,z1,z3,z251,z5,z210]),(0,[z1,z151,z3,z8,z11,z227]),(0,[z1163,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z208,z5,z60]),(0,[z161,z46,z3,z8,z5,z6]),(0,[z1,z224,z3,z8,z283,z6]),(0,[z1,z2,z3,z120,z5,z42]),(0,[z350,z1,z103,z8,z5,z6]),(1,[z1,z3,z729,z5,z6]),(0,[z396,z1,z2,z3,z8,z125]),(0,[z1,z2,z3,z1164,z5,z6])],[(0,[z1,z2,z3,z8,z1165,z6]),(0,[z1,z2,z3,z8,z5,z1166]),(0,[z1,z2,z3,z8,z17,z162]),(0,[z1167,z2,z3,z8,z5,z6]),(0,[z1168,z2,z3,z8,z5,z6]),(0,[z1,z1169,z3,z8,z5,z6])],[(0,[z1,z3,z8,z5,z6,z1170]),(0,[z1,z2,z3,z8,z5,z1171]),(0,[z1,z2,z437,z36,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1172]),(0,[z1,z98,z3,z8,z48,z60]),(0,[z1,z109,z2,z8,z585,z6]),(0,[z1,z109,z2,z158,z8,z42]),(0,[z1,z2,z3,z8,z1173,z6])],[(0,[z1,z2,z3,z8,z5,z20]),(0,[z1,z2,z1174,z8,z5,z6]),(0,[z1,z2,z3,z8,z1175,z6]),(0,[z1,z2,z3,z8,z346,z108])],[(0,[z1,z2,z3,z1176,z5,z6]),(0,[z1,z14,z3,z506,z48,z6]),(0,[z1,z3,z8,z5,z48,z60])],[(0,[z1,z2,z3,z1177,z5,z6]),(0,[z1,z2,z3,z8,z5,z1178]),(0,[z1,z2,z3,z1179,z5,z6]),(0,[z1,z3,z374,z8,z48,z60]),(0,[z287,z1,z2,z3,z5,z45])],[(0,[z1,z2,z3,z8,z172,z257]),(0,[z1,z2,z3,z1180,z5,z6]),(0,[z7,z2,z3,z92,z5,z6])],[(0,[z1,z2,z299,z8,z314,z6]),(0,[z1,z2,z3,z208,z5,z197]),(0,[z1,z2,z3,z8,z1181,z6])],[(0,[z0,z46,z3,z8,z5,z183]),(0,[z1,z2,z3,z8,z283,z42]),(0,[z1,z2,z3,z8,z1182,z6]),(0,[z1,z2,z3,z54,z11,z6])],[(0,[z1,z2,z3,z242,z48,z6]),(0,[z1,z2,z3,z134,z33,z6]),(0,[z1,z94,z103,z8,z5,z6]),(0,[z1,z2,z3,z8,z48,z167])],[(0,[z1,z2,z3,z411,z155,z6]),(0,[z2,z3,z8,z5,z770,z6]),(0,[z1,z2,z3,z8,z147,z138]),(0,[z1,z3,z8,z245,z48,z60]),(0,[z1,z114,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z1183])],[(0,[z1,z2,z3,z8,z1184,z6]),(0,[z1,z3,z89,z8,z48,z60])],[(0,[z1,z2,z3,z8,z1185,z6]),(0,[z1,z3,z8,z11,z645,z6]),(0,[z78,z2,z3,z8,z5,z382]),(0,[z1011,z2,z3,z8,z5,z6]),(0,[z1,z114,z3,z8,z1186,z6]),(0,[z263,z2,z3,z89,z5,z6])],[(0,[z1,z2,z3,z1160,z5,z6]),(0,[z1,z2,z168,z8,z5,z225]),(0,[z1,z1187,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z172,z6]),(0,[z1,z2,z3,z242,z5,z88]),(0,[z1,z2,z3,z73,z5,z42]),(0,[z1,z200,z2,z11,z107,z6]),(0,[z1,z643,z3,z8,z5,z60])],[(0,[z1,z224,z3,z8,z5,z88]),(0,[z1,z2,z3,z236,z5,z143]),(0,[z1,z3,z8,z48,z153,z60]),(0,[z81,z1,z2,z3,z134,z45])],[(0,[z1,z46,z352,z8,z5,z6]),(0,[z1,z2,z1188,z3,z8,z6]),(0,[z1,z1189,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z48,z250]),(0,[z1,z98,z3,z104,z5,z167]),(0,[z164,z1,z3,z8,z5,z812])],[(0,[z1,z2,z3,z8,z1190,z6]),(0,[z1,z2,z3,z8,z146,z60]),(0,[z1,z2,z35,z36,z48,z6]),(0,[z1,z2,z3,z570,z11,z6]),(0,[z1,z2,z3,z8,z626,z60]),(0,[z1,z2,z3,z8,z1191,z6]),(0,[z53,z1,z2,z54,z5,z37]),(0,[z193,z1,z2,z3,z8,z850])],[(0,[z1,z1094,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1192,z6])],[(0,[z0,z46,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z155,z60]),(0,[z69,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z1193,z8,z6]),(0,[z1,z2,z3,z8,z261,z60])],[(0,[z78,z2,z3,z8,z5,z118]),(0,[z1,z2,z937,z3,z8,z6])],[(0,[z1,z2,z3,z8,z1194,z6])],[(0,[z351,z2,z3,z8,z5,z118]),(0,[z1,z3,z506,z8,z48,z60]),(0,[z1195,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1196,z6]),(0,[z70,z114,z3,z8,z5,z6])],[(0,[z1,z2,z3,z134,z217,z6]),(0,[z1,z2,z3,z1197,z92,z6]),(0,[z1,z2,z3,z8,z5,z1198]),(0,[z1,z2,z3,z1199,z48,z6])],[(0,[z1,z2,z3,z8,z5,z1200]),(0,[z1,z3,z506,z48,z6,z60]),(0,[z397,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z943,z11,z6]),(0,[z185,z1,z2,z3,z8,z191]),(0,[z1,z2,z3,z8,z51,z60])],[(0,[z47,z2,z3,z8,z5,z43]),(0,[z85,z1,z3,z251,z290,z6]),(0,[z85,z1,z3,z251,z5,z138]),(0,[z1,z417,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z1201]),(0,[z1,z303,z3,z356,z5,z6]),(0,[z1,z2,z3,z8,z1202,z6])],[],[(0,[z510,z2,z21,z8,z5,z6]),(0,[z1,z3,z8,z5,z108,z60]),(0,[z1,z2,z3,z506,z554,z6]),(0,[z1,z19,z3,z8,z5,z60]),(1,[z1,z2,z8,z5,z859])],[(0,[z1,z2,z3,z1203,z5,z6]),(0,[z574,z2,z3,z217,z5,z6]),(0,[z93,z1,z103,z8,z48,z6]),(0,[z1,z2,z3,z8,z5,z1204]),(0,[z1,z511,z3,z8,z5,z125])],[(0,[z1,z2,z3,z242,z5,z6]),(0,[z1,z2,z3,z8,z5,z167]),(0,[z1,z2,z3,z8,z290,z42]),(0,[z1,z2,z3,z8,z17,z267]),(0,[z1,z2,z3,z8,z5,z1205])]],
   [[(0,[z1,z2,z3,z411,z48,z6]),(0,[z1,z3,z8,z48,z60,z360]),(0,[z1,z2,z3,z808,z5,z6]),(0,[z228,z2,z3,z8,z5,z43])],[(0,[z1,z2,z3,z8,z5,z1206]),(0,[z1,z2,z3,z405,z5,z42]),(0,[z1,z2,z3,z1031,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1207]),(0,[z1,z2,z3,z1208,z8,z6]),(0,[z91,z1,z3,z8,z48,z60]),(0,[z683,z2,z3,z8,z68,z6])],[(0,[z1,z2,z3,z1209,z5,z6]),(0,[z1,z3,z8,z11,z48,z42]),(0,[z1,z15,z3,z8,z48,z60])],[(0,[z1,z2,z3,z205,z5,z60]),(0,[z371,z2,z3,z8,z147,z6])],[(0,[z1,z2,z3,z1210,z8,z6]),(0,[z85,z1,z3,z251,z5,z6]),(0,[z1,z3,z104,z729,z5,z6]),(0,[z951,z2,z3,z8,z48,z6])],[(0,[z1,z1211,z3,z8,z5,z6]),(0,[z394,z2,z3,z405,z5,z6]),(0,[z1,z2,z3,z8,z5,z250]),(0,[z1,z2,z376,z8,z147,z6]),(0,[z1,z2,z3,z8,z5,z1212])],[(0,[z1,z2,z3,z8,z5,z1213]),(0,[z1,z2,z3,z134,z8,z9]),(0,[z1,z2,z35,z36,z5,z6]),(0,[z1,z114,z3,z356,z5,z6])],[(0,[z1,z2,z3,z217,z5,z179]),(0,[z1,z548,z3,z8,z48,z6])],[(0,[z0,z46,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1214,z6]),(0,[z1,z1215,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z48,z60])],[(0,[z291,z1,z2,z3,z506,z6]),(0,[z1,z3,z8,z48,z554,z60]),(0,[z1,z188,z2,z158,z8,z6]),(0,[z1,z2,z3,z8,z5,z1216])],[(0,[z1,z2,z299,z8,z11,z6]),(0,[z1,z2,z3,z8,z408,z42]),(0,[z71,z2,z21,z8,z5,z79]),(0,[z1,z3,z8,z5,z6,z812]),(0,[z1,z2,z3,z8,z6,z1217])],[(0,[z565,z1,z3,z8,z5,z60])],[(0,[z1,z2,z3,z1199,z5,z6]),(0,[z1,z2,z3,z8,z11,z517])],[(0,[z1,z2,z3,z8,z5,z1218]),(0,[z397,z2,z3,z8,z5,z6]),(0,[z94,z10,z3,z8,z5,z6])],[(0,[z1,z438,z3,z8,z11,z6]),(0,[z1059,z1,z2,z3,z8,z48]),(0,[z1,z2,z3,z8,z395,z416])]],
   [[(0,[z1,z98,z3,z104,z5,z60]),(0,[z1,z14,z3,z8,z11,z42])],[(0,[z1,z2,z1219,z8,z5,z6]),(0,[z1,z2,z3,z8,z48,z197]),(0,[z1,z244,z2,z3,z8,z60]),(0,[z1220,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z729,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1221]),(0,[z93,z1,z103,z8,z5,z6]),(0,[z1,z2,z129,z8,z147,z6]),(0,[z305,z1,z3,z8,z48,z64]),(0,[z1,z3,z8,z107,z48,z60]),(0,[z1,z2,z3,z8,z934,z6]),(0,[z1,z2,z3,z36,z134,z6])],[(0,[z1,z2,z3,z8,z11,z573]),(0,[z305,z1,z3,z8,z928,z6]),(0,[z1,z303,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z245,z267]),(0,[z1,z2,z3,z8,z252,z60])],[(0,[z1,z2,z3,z8,z5,z1222]),(0,[z1,z2,z3,z411,z5,z6])],[(0,[z1,z2,z3,z8,z1223,z6]),(0,[z85,z1,z376,z251,z5,z6]),(0,[z1224,z2,z3,z8,z5,z6]),(0,[z70,z2,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z1064,z6])],[(0,[z46,z3,z352,z8,z5,z6]),(0,[z71,z224,z21,z8,z5,z6]),(0,[z945,z2,z3,z8,z5,z6])],[(0,[z1,z2,z1225,z8,z5,z6]),(0,[z371,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z755,z5,z6]),(0,[z1,z2,z3,z867,z5,z42]),(0,[z1,z2,z3,z36,z163,z6])],[(0,[z1,z2,z3,z8,z5,z1226]),(0,[z1,z2,z3,z8,z1227,z6])],[(0,[z1,z2,z1228,z8,z5,z6]),(0,[z1,z300,z3,z8,z5,z88]),(0,[z1,z2,z3,z8,z1229,z6]),(0,[z1,z2,z3,z80,z8,z517]),(0,[z94,z2,z3,z49,z5,z6]),(0,[z1,z2,z376,z8,z5,z42]),(0,[z1,z2,z3,z8,z99,z201]),(0,[z951,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1230,z5,z6]),(0,[z1,z2,z3,z8,z1231,z6]),(0,[z1,z303,z3,z8,z759,z6]),(0,[z1,z2,z3,z8,z1232,z6])],[(0,[z91,z2,z3,z8,z121,z6]),(0,[z394,z2,z3,z8,z5,z327]),(0,[z1,z3,z73,z5,z48,z60]),(0,[z1,z2,z3,z5,z739,z6]),(0,[z1,z2,z437,z158,z8,z6])],[(0,[z1,z1233,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1234])],[(0,[z1,z2,z3,z8,z5,z60]),(0,[z94,z2,z3,z8,z11,z6]),(0,[z85,z1,z3,z729,z5,z6]),(0,[z1235,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z506,z48,z6]),(0,[z1,z3,z8,z279,z48,z60]),(0,[z1,z2,z3,z8,z11,z468])],[(0,[z1,z2,z1236,z8,z5,z6]),(0,[z71,z2,z21,z8,z5,z42]),(0,[z93,z1,z103,z8,z5,z327]),(0,[z1,z3,z8,z48,z6,z269]),(0,[z70,z2,z3,z8,z252,z6]),(0,[z1,z2,z3,z8,z1186,z6])]],
   [[(0,[z0,z46,z352,z8,z5,z6]),(0,[z1,z2,z3,z1237,z5,z6]),(0,[z1,z2,z3,z8,z5,z1238]),(0,[z1,z2,z995,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z183]),(0,[z85,z1,z129,z251,z5,z6]),(0,[z1,z3,z8,z48,z95,z60]),(0,[z1239,z2,z3,z8,z5,z6])],[(0,[z1,z1240,z3,z8,z5,z6]),(0,[z1,z2,z3,z311,z107,z6]),(0,[z287,z1,z3,z8,z48,z60]),(0,[z779,z2,z3,z8,z5,z60]),(0,[z1,z3,z100,z8,z5,z60]),(0,[z221,z2,z3,z54,z5,z6])],[(0,[z1,z2,z3,z8,z1241,z6]),(0,[z1,z2,z3,z242,z283,z6]),(0,[z1,z2,z3,z8,z17,z850])],[(0,[z215,z2,z21,z8,z5,z6]),(0,[z1,z2,z1242,z8,z5,z6]),(0,[z577,z2,z3,z8,z5,z118]),(0,[z1,z2,z3,z8,z390,z6]),(0,[z1,z2,z3,z356,z48,z6])],[(0,[z1,z2,z3,z8,z5,z197]),(0,[z30,z2,z3,z217,z11,z6]),(0,[z1,z2,z129,z8,z5,z42])],[(0,[z1,z2,z3,z1150,z5,z6]),(0,[z1,z2,z3,z1019,z5,z6]),(0,[z221,z2,z3,z8,z11,z6])],[(0,[z1,z995,z103,z8,z5,z6]),(0,[z1,z303,z3,z8,z5,z6]),(0,[z1,z56,z3,z8,z48,z60]),(0,[z1,z511,z3,z8,z11,z6]),(0,[z1,z3,z130,z8,z5,z60]),(0,[z396,z1,z2,z3,z80,z8]),(0,[z1,z2,z378,z8,z124,z6])],[(0,[z1,z300,z3,z8,z5,z6]),(0,[z1,z2,z3,z1243,z5,z6])],[(0,[z1,z2,z3,z8,z1244,z6]),(0,[z70,z2,z3,z8,z5,z6]),(0,[z263,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z6,z963])],[(0,[z1,z1245,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1246,z6]),(0,[z1,z2,z182,z3,z147,z6]),(0,[z1,z140,z3,z8,z48,z60]),(0,[z1,z2,z3,z8,z5,z850])],[(0,[z1,z3,z8,z48,z48,z60])],[(0,[z1,z2,z3,z4,z48,z6]),(0,[z173,z300,z3,z8,z5,z6]),(0,[z1,z3,z8,z585,z5,z60]),(0,[z1,z194,z2,z284,z3,z6])],[(0,[z1,z2,z3,z49,z11,z6]),(0,[z1,z2,z3,z8,z1247,z6])],[(0,[z1,z2,z3,z8,z1248,z6]),(0,[z1249,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z356,z252,z6])],[(0,[z173,z2,z254,z8,z5,z6]),(0,[z1,z244,z2,z3,z80,z6])]],
   [[(0,[z1,z2,z3,z8,z1250,z6]),(1,[z94,z103,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z64]),(0,[z1,z2,z3,z54,z321,z6]),(0,[z1,z2,z3,z8,z5,z1251])],[(0,[z1,z534,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z1252,z6]),(0,[z1253,z2,z3,z8,z5,z6]),(0,[z1254,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z1255]),(0,[z1,z2,z3,z8,z348,z60])],[(0,[z1,z459,z2,z158,z8,z6]),(0,[z1,z2,z3,z506,z5,z6]),(1,[z1,z3,z8,z5,z812]),(0,[z81,z263,z2,z3,z5,z45])],[(0,[z1,z2,z3,z73,z48,z60]),(0,[z1256,z1,z2,z3,z8,z5]),(0,[z1,z511,z3,z80,z8,z6])],[(0,[z1,z2,z352,z8,z5,z60]),(0,[z1,z2,z3,z8,z11,z79]),(0,[z1,z1257,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1258,z6]),(0,[z1,z2,z3,z8,z770,z6]),(0,[z193,z221,z2,z3,z8,z5]),(0,[z1,z303,z3,z8,z5,z551])],[(0,[z1,z2,z3,z8,z1259,z6]),(0,[z1,z2,z3,z8,z346,z42]),(0,[z1,z2,z3,z134,z8,z60])],[(0,[z1,z2,z3,z999,z5,z42]),(0,[z1,z1260,z3,z8,z5,z6])],[(1,[z46,z352,z8,z5,z6]),(0,[z1,z2,z3,z73,z506,z6]),(0,[z1,z2,z3,z1261,z5,z6])],[(0,[z1,z2,z3,z92,z11,z6]),(0,[z1,z2,z3,z120,z5,z60]),(0,[z7,z2,z3,z8,z5,z737]),(0,[z1,z2,z1262,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1263]),(0,[z305,z1,z3,z8,z48,z573]),(0,[z1,z2,z3,z356,z5,z6]),(0,[z396,z1,z2,z3,z8,z321])],[(0,[z1,z1264,z3,z8,z5,z6]),(0,[z59,z1,z3,z8,z48,z60])],[(0,[z1,z3,z103,z8,z5,z257]),(0,[z1,z3,z103,z8,z11,z60]),(0,[z53,z1,z2,z8,z11,z37]),(0,[z1,z716,z3,z8,z5,z124])],[(0,[z1,z2,z1265,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z1266]),(0,[z1,z2,z3,z8,z5,z1267]),(0,[z1,z2,z3,z8,z11,z108])],[(0,[z1,z300,z3,z8,z802,z6]),(0,[z1,z224,z3,z8,z920,z6]),(0,[z1,z1268,z3,z8,z5,z6])],[(0,[z1,z2,z204,z8,z124,z6]),(0,[z2,z3,z8,z5,z9,z737]),(0,[z1,z2,z3,z8,z1269,z6]),(0,[z1,z2,z3,z80,z279,z42]),(0,[z1,z2,z3,z1270,z5,z6]),(0,[z1,z2,z3,z1271,z5,z6])],[(0,[z71,z300,z21,z8,z5,z6]),(0,[z1,z2,z3,z1272,z5,z6]),(0,[z1,z1273,z2,z3,z8,z6])],[(0,[z516,z2,z3,z8,z5,z118]),(0,[z1,z2,z3,z8,z5,z1274]),(0,[z1,z2,z3,z8,z1275,z6]),(0,[z1,z2,z3,z8,z1276,z6]),(0,[z1,z2,z3,z8,z1106,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z8,z283,z60]),(0,[z1277,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z405,z5,z250]),(0,[z1,z2,z182,z3,z506,z6]),(0,[z1,z2,z3,z1278,z8,z6])],[(0,[z1,z126,z352,z8,z5,z6]),(0,[z1,z2,z3,z4,z408,z6]),(0,[z1,z2,z3,z8,z1279,z6])],[(0,[z1,z2,z3,z8,z5,z1280]),(0,[z1,z200,z2,z107,z48,z6]),(0,[z1,z2,z3,z893,z5,z42]),(0,[z1,z317,z3,z8,z5,z42])],[(0,[z1281,z2,z3,z8,z5,z6]),(0,[z53,z1,z2,z8,z5,z473]),(0,[z1,z2,z3,z54,z5,z42])],[(0,[z30,z244,z2,z3,z217,z6]),(0,[z1,z3,z8,z346,z6,z60])],[(0,[z1,z2,z3,z8,z343,z42]),(0,[z1,z654,z3,z8,z11,z6]),(0,[z1,z3,z8,z5,z42,z60])],[(0,[z1,z2,z3,z1197,z8,z6]),(0,[z94,z2,z3,z8,z315,z6]),(0,[z69,z2,z3,z80,z5,z6]),(0,[z1,z2,z3,z8,z48,z1282]),(0,[z1,z2,z3,z73,z5,z60]),(0,[z1,z14,z3,z8,z261,z6]),(0,[z396,z1,z2,z3,z8,z5])],[(0,[z1,z2,z3,z411,z5,z88]),(0,[z2,z3,z8,z92,z5,z118]),(0,[z47,z2,z3,z8,z5,z737]),(0,[z1,z2,z3,z8,z11,z42]),(0,[z1,z151,z3,z8,z48,z60]),(0,[z193,z1,z2,z3,z8,z191])],[(0,[z1,z1283,z3,z8,z5,z6]),(0,[z32,z2,z3,z8,z5,z179]),(0,[z1,z2,z3,z8,z1284,z6]),(0,[z1,z3,z8,z661,z11,z6]),(0,[z1,z2,z3,z1285,z8,z6])],[(0,[z1,z2,z3,z8,z5,z1286])],[(0,[z32,z2,z3,z675,z5,z6]),(0,[z1122,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z208,z5,z183]),(0,[z1,z300,z3,z8,z283,z6]),(0,[z1,z2,z3,z1287,z5,z6])],[(1,[z2,z3,z217,z5,z179]),(0,[z1,z2,z3,z1288,z5,z6]),(0,[z93,z1,z103,z405,z5,z6]),(0,[z1,z174,z2,z5,z107,z6]),(1,[z1,z3,z8,z48,z64]),(0,[z81,z1,z2,z3,z48,z45]),(0,[z1,z2,z3,z570,z5,z42])],[(0,[z0,z46,z3,z8,z408,z6]),(0,[z1,z1289,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1290,z6]),(1,[z1,z3,z8,z928,z6]),(0,[z116,z1,z3,z8,z48,z6]),(0,[z935,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z163,z8,z6])],[(0,[z1,z2,z110,z8,z5,z16]),(0,[z1,z303,z3,z8,z5,z37])]],
   [[(0,[z1,z3,z8,z5,z83,z60]),(0,[z1,z2,z3,z134,z8,z118]),(0,[z7,z2,z3,z8,z48,z9])],[(0,[z1,z2,z3,z8,z1291,z6])],[(0,[z519,z2,z3,z217,z5,z6]),(0,[z1,z2,z3,z1292,z8,z6]),(0,[z32,z2,z3,z33,z48,z6]),(0,[z1,z2,z3,z8,z99,z42]),(0,[z1,z2,z3,z8,z11,z201]),(0,[z1,z476,z3,z8,z11,z6]),(0,[z1,z2,z182,z937,z3,z6])],[(0,[z1293,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z1294,z5,z6]),(0,[z1,z2,z3,z8,z1295,z6]),(0,[z1,z2,z3,z163,z107,z6])],[(0,[z1,z2,z3,z8,z5,z1296])],[(0,[z1,z2,z3,z169,z11,z6])],[(0,[z1,z2,z3,z8,z290,z60]),(0,[z1,z2,z3,z8,z17,z477])],[(0,[z1,z2,z3,z8,z1297,z6]),(0,[z1,z2,z352,z4,z5,z6]),(0,[z1,z2,z3,z208,z48,z6]),(0,[z1,z2,z3,z1298,z8,z6]),(0,[z1,z2,z3,z49,z315,z6]),(0,[z1,z2,z3,z8,z5,z1299])],[(0,[z1,z2,z3,z8,z1300,z6]),(0,[z71,z2,z21,z242,z5,z6]),(0,[z30,z2,z3,z217,z5,z31]),(0,[z439,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z405,z5,z60]),(0,[z1,z200,z2,z5,z107,z42])],[(0,[z1,z2,z3,z8,z5,z1301]),(0,[z1,z2,z3,z1302,z8,z6]),(0,[z262,z1,z3,z8,z48,z6]),(0,[z1,z2,z3,z5,z6,z764]),(0,[z1256,z1,z2,z3,z8,z11]),(0,[z1,z2,z3,z5,z42,z876])],[(0,[z1,z3,z295,z8,z5,z60]),(0,[z1,z2,z3,z8,z5,z1303]),(0,[z1,z2,z3,z1304,z5,z6]),(0,[z1,z3,z8,z11,z48,z60])],[(0,[z1,z2,z3,z8,z5,z1282]),(0,[z1,z14,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z11,z1159])],[(0,[z7,z2,z3,z8,z5,z153]),(0,[z1305,z2,z3,z8,z5,z6]),(0,[z1,z151,z3,z8,z5,z60])],[(0,[z1,z391,z2,z3,z73,z6]),(0,[z1,z151,z3,z8,z11,z468]),(0,[z1,z19,z3,z8,z626,z6]),(0,[z1,z1306,z3,z8,z5,z6]),(0,[z193,z1,z19,z3,z8,z125])],[],[(0,[z1,z2,z3,z8,z5,z1307]),(0,[z1,z224,z3,z8,z5,z979]),(0,[z1,z2,z3,z405,z390,z6]),(0,[z1,z3,z8,z48,z16,z60]),(0,[z1,z2,z3,z1308,z5,z6])]],
   [[(0,[z1,z2,z3,z1309,z5,z6]),(0,[z1310,z2,z3,z8,z5,z6]),(0,[z1,z303,z3,z8,z252,z6]),(0,[z1,z2,z3,z5,z767,z45])],[(0,[z1,z2,z3,z8,z5,z1311]),(0,[z1,z2,z3,z8,z5,z1312]),(0,[z53,z1,z2,z598,z8,z5]),(0,[z81,z1,z2,z3,z5,z45]),(0,[z1,z2,z3,z8,z1313,z6])],[(0,[z1,z2,z3,z8,z408,z60]),(0,[z1,z2,z3,z8,z1314,z6]),(0,[z1,z114,z3,z8,z48,z6]),(0,[z1,z2,z3,z8,z1315,z6]),(0,[z1,z2,z3,z8,z5,z1316]),(0,[z1,z2,z8,z5,z859,z37]),(0,[z1,z2,z3,z80,z556,z6])],[(0,[z1,z2,z3,z8,z5,z1317])],[(0,[z1,z2,z3,z8,z11,z31]),(0,[z1,z3,z8,z48,z60,z37])],[(0,[z1,z2,z299,z8,z5,z42]),(0,[z1,z2,z3,z8,z343,z20]),(0,[z1,z2,z3,z8,z5,z1090]),(0,[z1,z2,z3,z1318,z5,z6]),(0,[z1,z194,z2,z3,z205,z6]),(0,[z1,z3,z8,z395,z48,z60]),(0,[z1,z3,z8,z48,z60,z45]),(0,[z1,z2,z3,z8,z5,z852])],[(0,[z1,z3,z8,z334,z5,z60]),(0,[z1,z10,z3,z8,z146,z60]),(0,[z1,z643,z3,z8,z48,z6]),(0,[z1,z2,z3,z1042,z8,z6]),(0,[z1,z2,z3,z8,z5,z1319])],[(0,[z1,z2,z3,z8,z1320,z6]),(0,[z1,z2,z3,z8,z5,z1321]),(0,[z1,z2,z3,z8,z1322,z6])],[(0,[z1,z2,z3,z8,z5,z1323]),(0,[z1,z2,z3,z750,z5,z6]),(0,[z69,z2,z3,z251,z5,z6]),(0,[z396,z1,z716,z3,z8,z5]),(0,[z1,z2,z3,z1324,z5,z6])],[(0,[z1,z2,z3,z8,z314,z42]),(0,[z2,z534,z3,z217,z5,z6]),(0,[z1,z2,z3,z8,z1325,z6]),(0,[z1,z3,z8,z5,z346,z60])],[(0,[z1,z2,z3,z8,z408,z197]),(0,[z673,z1,z103,z8,z5,z6]),(1,[z2,z3,z750,z5,z6]),(0,[z1,z632,z3,z8,z11,z6])],[(0,[z1,z2,z3,z208,z5,z6]),(0,[z1,z2,z3,z1326,z8,z6]),(0,[z1,z2,z3,z8,z5,z1327]),(0,[z1,z2,z56,z405,z5,z6]),(0,[z69,z2,z3,z8,z48,z6])],[(0,[z1,z2,z3,z8,z5,z1328]),(0,[z1,z2,z1329,z8,z5,z6]),(0,[z1,z2,z3,z1095,z11,z6]),(0,[z1,z2,z528,z36,z5,z6]),(0,[z1,z114,z3,z8,z252,z6])],[(0,[z1,z2,z3,z208,z408,z6]),(0,[z142,z126,z3,z8,z5,z60]),(0,[z71,z2,z21,z411,z5,z6]),(0,[z1,z2,z3,z8,z5,z1330]),(0,[z2,z3,z8,z5,z6,z737]),(0,[z1,z2,z3,z8,z387,z201]),(0,[z305,z1,z3,z8,z48,z42]),(0,[z396,z1,z2,z3,z8,z11])],[(0,[z1,z1331,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1332,z6]),(0,[z371,z2,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z1083,z6])],[(0,[z1,z2,z3,z1028,z5,z6]),(0,[z1,z2,z3,z8,z60,z1255]),(0,[z1,z2,z3,z8,z989,z42])]],
   [[(0,[z1,z224,z3,z8,z5,z1073]),(0,[z1,z2,z376,z8,z5,z60]),(0,[z1,z2,z3,z8,z48,z713]),(0,[z1,z2,z3,z8,z52,z48]),(0,[z53,z1,z2,z8,z5,z859])],[(0,[z1,z2,z3,z8,z5,z1333]),(0,[z1,z2,z3,z8,z5,z1334]),(0,[z1,z2,z3,z8,z5,z1335])],[(0,[z1,z1336,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z315,z42]),(0,[z1,z3,z105,z8,z11,z6])],[(0,[z1,z2,z3,z8,z1337,z6]),(0,[z1,z2,z3,z8,z5,z1338]),(0,[z1,z2,z1339,z8,z5,z6]),(0,[z1,z19,z3,z8,z48,z6])],[(0,[z1,z2,z3,z8,z48,z183]),(0,[z1,z2,z3,z8,z390,z327])],[(0,[z1,z2,z3,z8,z5,z1340]),(0,[z69,z2,z3,z8,z5,z138])],[(0,[z71,z2,z21,z8,z5,z60]),(0,[z1,z2,z3,z1341,z5,z6]),(0,[z1,z114,z3,z8,z5,z6]),(0,[z1070,z2,z3,z8,z5,z42]),(0,[z1,z2,z563,z8,z124,z6])],[(0,[z94,z2,z3,z8,z5,z42])],[(0,[z30,z2,z3,z217,z5,z179]),(0,[z78,z1,z3,z8,z48,z60]),(0,[z1,z3,z8,z5,z42,z447])],[(0,[z1,z10,z3,z8,z5,z250]),(0,[z1,z2,z1342,z8,z5,z6])],[(0,[z1,z2,z3,z205,z48,z6]),(0,[z1,z2,z3,z236,z5,z517]),(0,[z1,z103,z8,z5,z107,z60]),(0,[z53,z221,z2,z8,z5,z37])],[(0,[z1,z2,z3,z411,z283,z6]),(0,[z1,z1343,z3,z8,z5,z6]),(0,[z1,z3,z8,z48,z60,z145]),(0,[z599,z1,z2,z3,z8,z199]),(0,[z1,z3,z158,z8,z48,z60]),(0,[z1,z322,z3,z8,z48,z6])],[(0,[z1,z10,z3,z8,z48,z60]),(0,[z1,z2,z129,z8,z5,z60]),(0,[z1,z13,z2,z182,z3,z6]),(0,[z1,z304,z3,z8,z5,z60]),(0,[z1,z2,z3,z8,z17,z416]),(0,[z1344,z2,z3,z8,z5,z6])],[(0,[z1,z583,z3,z8,z5,z42]),(0,[z1,z2,z3,z8,z626,z6]),(0,[z1,z2,z15,z8,z11,z16])],[(0,[z1,z109,z2,z158,z8,z60]),(0,[z1,z2,z3,z8,z5,z1345])],[(0,[z1,z2,z352,z8,z5,z197]),(0,[z69,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z155,z6]),(0,[z30,z2,z3,z217,z5,z42]),(0,[z1,z3,z8,z48,z6,z64]),(0,[z1,z2,z3,z8,z261,z6]),(0,[z1,z2,z1346,z8,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 496) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 496).take 489) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 985).take 461) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1446)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [496, 489, 461] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 101).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 210).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 304).take 97).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 401).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 501).take 11).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [101, 109, 94, 97, 100, 11] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38067

theorem PEqualNP.Outside.L_meta_38067 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276682376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276682376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38067.solve
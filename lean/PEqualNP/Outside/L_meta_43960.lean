import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43960

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
  Nat.testBit (4276813032 * 2 ^ 32 + 4276797568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0838c06e210ae1a1#64 ++ 0x00107180dc4215c3#64 ++ 0x19f8c0fe231fe3de#64 ++ 0xec33f181fc463fc7#64 : BitVec 256),
   (0x22805b142c662eca#64 ++ 0x044500b62858cc5d#64 ++ 0x6680ff1c3ce67ffd#64 ++ 0xb4cd01fe3879ccff#64 : BitVec 256),
   (0x850b05a2c0b8570c#64 ++ 0x090a160b458170ae#64 ++ 0x871f07e3c0f87ffb#64 ++ 0xff0e3e0fc781f0ff#64 : BitVec 256),
   (0x581de80377007870#64 ++ 0x12b03bd006ee00f0#64 ++ 0xf81ff803ff007c77#64 ++ 0xdbf03ff007fe00f8#64 : BitVec 256),
   (0xf7c000019ad50000#64 ++ 0x03ef80000335aa00#64 ++ 0xffe00003ffff804f#64 ++ 0x9fffc00007ffff00#64 : BitVec 256),
   (0xfff6b6d800000000#64 ++ 0x23ffed6db0000000#64 ++ 0xfffffffc0000003f#64 ++ 0xe3fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 3]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [13, 11]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x19f8c0fe231fe3de 0xec33f181fc463fc7

def z1 : W := mkw 0x2280000008440000 0x0045000000108800 0x0680000000e60008 0x040d00000001cc00

def z2 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6680ff1c3ce67ffd 0xb4cd01fe3879ccff

def z3 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf81ff803ff007c77 0xdbf03ff007fe00f8

def z4 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x871f07e3c0f87ffb 0xff0e3e0fc781f0ff

def z5 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xffe00003ffff804f 0x9fffc00007ffff00

def z6 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffc0000003f 0xe3fffffff8000000

def z7 : W := mkw 0xf7c013159af7068a 0x07ef80262b35ee0d 0xffe0071fffff83cf 0xbfffc00e3fffff07

def z8 : W := mkw 0x2ab8db7e2d6eefeb 0x045571b6fc5adddf 0x7ff8fffe3fffffff 0xfcfff1fffc7fffff

def z9 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xf9fff8ffff1fffff 0xfff3fff1fffe3fff

def z10 : W := mkw 0xa78b1fb2ccfc5f4e 0x0d4f163f6599f8be 0xe71f3fe3dcf87ffb 0xffce3e7fc7b9f0ff

def z11 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x001ffffc00000030 0x60003ffff8000000

def z12 : W := mkw 0x85030580c0b0160c 0x090a060b0181602c 0x86070701c0e01c21 0x130c0e0e0381c038

def z13 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x861f07e1c0e07fb1 0x730c3e0fc381c0ff

def z14 : W := mkw 0x5814e80024002840 0x02b029d000480050 0xf81ff8003c007c77 0xd3f03ff0007800f8

def z15 : W := mkw 0x7af4b25800000000 0x22f5e964b0000000 0x79f8f8fc0000001e 0xe0f3f1f1f8000000

def z16 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x18f8c0fc2307e394 0x6031f181f8460fc7

def z17 : W := mkw 0x0838806e010ac1a1 0x00107100dc021583 0x19f800fe031f838a 0x6c33f001fc063f07

def z18 : W := mkw 0x000049042c662eca 0x040000920858cc5d 0x000000003ce67fc0 0x140000000079ccff

def z19 : W := mkw 0x2280121000000000 0x0045002420000000 0x6680ff1c0000003d 0xa0cd01fe38000000

def z20 : W := mkw 0x7af4b2591a450000 0x22f5e964b2348a00 0x78e0f81c3f078004 0x00f1c1f0387e0f00

def z21 : W := mkw 0xdd1feda3f7b87f7c 0x1bba3fdb47ef70fe 0xff1fffe3fff87fff 0xfffe3fffc7fff0ff

def z22 : W := mkw 0x22805a142c4628c2 0x044500b428588c51 0x6080f81c3c060004 0x00c101f038780c00

def z23 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xe0073801dc001c21 0x13c00e7003b80038

def z24 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xe6000003ffff8041 0x1fcc000007ffff00

def z25 : W := mkw 0x0000480024002840 0x0000009000480050 0x6000f8003c007c75 0x90c001f0007800f8

def z26 : W := mkw 0x7a9dfb177f667efa 0x16f53bf62efeccfd 0xfe9fff1fffe67fff 0xfffd3ffe3fffccff

def z27 : W := mkw 0xa7c0131488f7068a 0x054f80262911ee0d 0x07e0071c00ff8388 0x240fc00e3801ff07

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000003c0000043 0x9b00000007800000

def z29 : W := mkw 0x0009000240005000 0x00001200048000a0 0x801f0003c0007c73 0xdb003e00078000f8

def z30 : W := mkw 0xf7c2048000000000 0x03ef840900000000 0xffff07e00000003f 0xe3fffe0fc0000000

def z31 : W := mkw 0x72c000011a450000 0x02e5800002348a00 0x78e000003f078004 0x00f1c000007e0f00

def z32 : W := mkw 0xf7c04005bad72080 0x03ef80800b75ae41 0xffe0c01fffffe3df 0xbfffc1803fffffc7

def z33 : W := mkw 0xdd7ea4ea0108c121 0x23bafd49d4021182 0x997f00e203198002 0x4b32fe01c4063300

def z34 : W := mkw 0x228013140866068a 0x044500262810cc0d 0x0680071c00e60388 0x240d000e3801cc07

def z35 : W := mkw 0x581da00353005030 0x12b03b4006a600a0 0x981f0003c3000002 0x4b303e0007860000

def z36 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x811f00e3c0f87fc2 0x5f023e01c781f0ff

def z37 : W := mkw 0x000000019ad50000 0x000000000335aa00 0x00000003ffff8040 0x1c00000007ffff00

def z38 : W := mkw 0x72857b157e663eda 0x16e50af62afccc7d 0xe687ff1dfce67ffd 0xb7cd0ffe3bf9ccff

def z39 : W := mkw 0xa782169000000000 0x014f042d20000000 0xe79ffffc0000003f 0xe3cf3ffff8000000

def z40 : W := mkw 0xa78b5fb6ecfe7fce 0x0d4f16bf6dd9fcff 0xe79ffffffcfe7fff 0xffcf3ffffff9fcff

def z41 : W := mkw 0x850b04a2c0985104 0x090a1609458130a2 0x871f00e3c0f8004b 0xdf0e3e01c781f000

def z42 : W := mkw 0x7a94fb153f662efa 0x16f529f62a7ecc5d 0x7e80ff1c3fe67ffd 0xb4fd01fe387fccff

def z43 : W := mkw 0x00090122c0b8570c 0x08001202458170ae 0x00000003c0f87fc0 0x1c0000000781f0ff

def z44 : W := mkw 0x7af4b25800000000 0x22f5e964b0000000 0x78e0f81c00000004 0x00f1c1f038000000

def z45 : W := mkw 0x581de80265007870 0x12b03bd004ca00f0 0xf81ff80000007c37 0xc3f03ff0000000f8

def z46 : W := mkw 0xa7c0000088d50000 0x014f80000111aa00 0x07e0000000ff8008 0x040fc0000001ff00

def z47 : W := mkw 0x00004804240228c0 0x0000009008480451 0x6080f81c3c067ffd 0xb4c101f038780cff

def z48 : W := mkw 0x8502058080b0060c 0x090a040b0101600c 0x0600070000e00000 0x000c000e0001c000

def z49 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xe6000001dce00001 0x13cc000003b9c000

def z50 : W := mkw 0xfff8c06fbbdfe1a1 0x03fff180df77bfc3 0xfff8c0ffffffe3df 0xfffff181ffffffc7

def z51 : W := mkw 0x2280121408460082 0x0445002428108c01 0x0080001c00060000 0x0001000038000c00

def z52 : W := mkw 0x581de9077f667efa 0x16b03bd20efeccfd 0xf81ff803ffe67ff7 0xdff03ff007ffccff

def z53 : W := mkw 0x0830c06c210aa1a1 0x00106180d8421543 0x19e0c0fc231f838c 0x2433c181f8463f07

def z54 : W := mkw 0xfff6b6fc000a8181 0x23ffed6df8001503 0xfffffffc001f83bf 0xe7fffffff8003f07

def z55 : W := mkw 0x00005b1424222eca 0x040000b62848445d 0x0000ff1c00007fb0 0x200001fe380000ff

def z56 : W := mkw 0xfff6ffdc2c662eca 0x27ffedffb858cc5d 0xfffffffc3ce67fff 0xf7fffffff879ccff

def z57 : W := mkw 0xfffffeda65007870 0x33fffffdb4ca00f0 0xfffffffc00007c3f 0xe3fffffff80000f8

def z58 : W := mkw 0x000b05a2c0b8570c 0x0800160b458170ae 0x001f07e3c0f87ff0 0x7c003e0fc781f0ff

def z59 : W := mkw 0xf7c0000000000000 0x03ef800000000000 0xffe000000000000f 0x83ffc00000000000

def z60 : W := mkw 0x22805b15bef72eca 0x044500b62b7dee5d 0x6680ff1ffffffffd 0xbccd01fe3fffffff

def z61 : W := mkw 0x22805a142c4628c2 0x044500b428588c51 0x6080f81c3c0663dc 0xa4c101f038780cc7

def z62 : W := mkw 0xdd1fa4a3d3985134 0x1bba3f4947a730a2 0x991f00e3c3180002 0x4b323e01c7863000

def z63 : W := mkw 0x0020006c000a8181 0x00004000d8001503 0x19e000fe231f83ce 0xac33c001fc463f07

def z64 : W := mkw 0x081de80377007870 0x10103bd006ee00f0 0x001ff803ff007c70 0x58003ff007fe00f8

def z65 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xe6800001fce6004d 0x97cd000003f9cc00

def z66 : W := mkw 0x0005280044001850 0x10000a5000880030 0x0007380000001c20 0x00000e7000000038

def z67 : W := mkw 0x002216d800000000 0x2000442db0000000 0x000007fc00000000 0x2000000ff8000000

def z68 : W := mkw 0x00084026210ae1a1 0x000010804c4215c3 0x00000002231fe3c0 0x0c00000004463fc7

def z69 : W := mkw 0xf7c6369000000000 0x23ef8c6d20000000 0xe6073f0000000021 0x03cc0e7e00000000

def z70 : W := mkw 0x083ef6fe210ae1a1 0x20107dedfc4215c3 0x19fffffe231fe3fe 0xec33fffffc463fc7

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000f80000000035 0x80c001f000000000

def z72 : W := mkw 0xf7c0121000000000 0x03ef802420000000 0xffe0ff1c0000003f 0xa3ffc1fe38000000

def z73 : W := mkw 0x850205a080b8070c 0x090a040b4101700e 0x070007e000f80388 0x240e000fc001f007

def z74 : W := mkw 0x0000000000000000 0x0000000000000000 0x008000002006004c 0x8401000000400c00

def z75 : W := mkw 0xd546248000000000 0x23aa8c4900000000 0x8007000000000000 0x03000e0000000000

def z76 : W := mkw 0x0008002200084100 0x0000100044001082 0x011800e2001863da 0xec023001c40030c7

def z77 : W := mkw 0x8d3bc5eee1baf7ad 0x091a778bddc375ef 0x9fffc7ffe3ffffff 0xff3fff8fffc7ffff

def z78 : W := mkw 0x850b04a2c0985104 0x090a1609458130a2 0x811f00e3c0180002 0x4b023e01c7803000

def z79 : W := mkw 0x5000000112000000 0x02a0000002240000 0x780000003f000004 0x00f00000007e0000

def z80 : W := mkw 0xf7c05b15bef72eca 0x07ef80b62b7dee5d 0xffe0ff1fffffffff 0xbfffc1fe3fffffff

def z81 : W := mkw 0x22805a1024002840 0x004500b420480050 0x6680ff1c3c007c7d 0xb0cd01fe387800f8

def z82 : W := mkw 0x083ffeda65007870 0x30107ffdb4ca00f0 0x001ffffc00007c30 0x60003ffff80000f8

def z83 : W := mkw 0xdd1fec8377007870 0x13ba3fd906ee00f0 0xff1fffe3ff007c7f 0xfbfe3fffc7fe00f8

def z84 : W := mkw 0x5009480377007870 0x12a0129006ee00f0 0xf8000003ff007c47 0x9bf0000007fe00f8

def z85 : W := mkw 0x8500010080b00608 0x010a00020101600c 0x87000703c0f87ffb 0xbf0e000e0781f0ff

def z86 : W := mkw 0x00090123dafd570c 0x0800120247b5faae 0x00000003ffffffc0 0x1c00000007ffffff

def z87 : W := mkw 0xffdde80377007870 0x13ffbbd006ee00f0 0xfffff803ff007c7f 0xdbfffff007fe00f8

def z88 : W := mkw 0x5814a00112000000 0x02b0294002240000 0xf81ff803ff000077 0xdbf03ff007fe0000

def z89 : W := mkw 0x0000400420022080 0x0000008008400441 0x0080c01c200663dc 0xa401018038400cc7

def z90 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xffffffffffff807f 0xffffffffffffff00

def z91 : W := mkw 0x0020006c000a8181 0x00004000d8001503 0x01e000fc001f8388 0x2403c001f8003f07

def z92 : W := mkw 0x000b05a24028570c 0x0800160b448050ae 0x001f07e000007fb0 0x60003e0fc00000ff

def z93 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xe61ffffc00000031 0x63cc3ffff8000000

def z94 : W := mkw 0xdd76b6d800000000 0x23baed6db0000000 0x997ffffc00000032 0x6332fffff8000000

def z95 : W := mkw 0x0836ffdc24222eca 0x24106dffb848445d 0x001ffffc00007fb0 0x60003ffff80000ff

def z96 : W := mkw 0x0008002200084100 0x0000100044001082 0x00000002001863c0 0x0c000000040030c7

def z97 : W := mkw 0xf7cb04a3dadd5104 0x0bef960947b5baa2 0xffff00e3ffff804f 0xdffffe01c7ffff00

def z98 : W := mkw 0xffffb6fac0985104 0x2bffff6df58130a2 0xffffffffc018003f 0xebffffffff803000

def z99 : W := mkw 0x8500000080900000 0x010a000001012000 0x87000003c0f8004b 0x9f0e00000781f000

def z100 : W := mkw 0x228b5fb66c6e7fce 0x0c4516bf6cd8dcff 0x669ffffc3ce67ffd 0xf4cd3ffff879ccff

def z101 : W := mkw 0x081de80265007870 0x10103bd004ca00f0 0x801ff803c0007c73 0xdb003ff0078000f8

def z102 : W := mkw 0xfff6f6dc20022080 0x23ffededb8400441 0xfffffffc200663ff 0xe7fffffff8400cc7

def z103 : W := mkw 0xa7c2169000000000 0x214f842d20000000 0x0600070000000000 0x000c000e00000000

def z104 : W := mkw 0x5814e80137002870 0x12b029d0026e0050 0x7800f8003f000004 0x00f001f0007e0000

def z105 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x0018c0fc00006390 0x60003181f80000c7

def z106 : W := mkw 0x0000010000200608 0x000000020000400c 0x0000070000007fb0 0x2000000e000000ff

def z107 : W := mkw 0x581da00353005030 0x12b03b4006a600a0 0xf81ff803c3000037 0xcbf03ff007860000

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x19e00002231f804e 0x8c33c00004463f00

def z109 : W := mkw 0xfffef6fe210ae1a1 0x23fffdedfc4215c3 0xfffffffe231fe3ff 0xeffffffffc463fc7

def z110 : W := mkw 0x081da00241005030 0x10103b40048200a0 0x001f000000000000 0x40003e0000000000

def z111 : W := mkw 0xf7c000011a450000 0x03ef800002348a00 0xffe000003f07800f 0x83ffc000007e0f00

def z112 : W := mkw 0x85030580c0b0160c 0x090a060b0181602c 0x86070701c0e07ff9 0xb70c0e0e0381c0ff

def z113 : W := mkw 0x5836b6d800000000 0x22b06d6db0000000 0xf81ffffc00000037 0xe3f03ffff8000000

def z114 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0x781ff8003f007c34 0x40f03ff0007e00f8

def z115 : W := mkw 0x2280121008440000 0x0045002420108800 0x6680ff1c3ce6007d 0xb4cd01fe3879cc00

def z116 : W := mkw 0x5005680176003850 0x12a00ad002ec0070 0xe007f801fc007c75 0x93c00ff003f800f8

def z117 : W := mkw 0x0001000040001000 0x0000020000800020 0x80070001c0001c21 0x13000e0003800038

def z118 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6080ff1c3c067fb4 0x20c101fe38780cff

def z119 : W := mkw 0x000901224028570c 0x08001202448050ae 0x0000000000007f80 0x00000000000000ff

def z120 : W := mkw 0x0000400020002000 0x0000008000400040 0x0000c00020006054 0x80000180004000c0

def z121 : W := mkw 0x5834e84d3702a8f1 0x12b069d09a6e0551 0x78e0f81c3f078004 0x00f1c1f0387e0f00

def z122 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000000e00049 0x940c00000001c000

def z123 : W := mkw 0xf7c30581daf5160c 0x0bef860b03b5ea2c 0xe6070701dce01c21 0x13cc0e0e03b9c038

def z124 : W := mkw 0x72c0000000000000 0x02e5800000000000 0x78e0000000000004 0x00f1c00000000000

def z125 : W := mkw 0x850b45a6e1baf7ad 0x090a168b4dc375ef 0x871f07e3e3fffffb 0xff0e3e0fc7c7ffff

def z126 : W := mkw 0xa7825fb4acfe2fce 0x0d4f04bf6959fc5f 0x6780fffc3cfe7ffd 0xb4cf01fff879fcff

def z127 : W := mkw 0xa7e216d800000000 0x214fc42db0000000 0x07e007fc00000008 0x200fc00ff8000000

def z128 : W := mkw 0xfffffedb77007870 0x33fffffdb6ee00f0 0xffffffffff007c7f 0xfbfffffffffe00f8

def z129 : W := mkw 0xdd76a4c800000000 0x23baed4990000000 0x997f00e000000002 0x4332fe01c0000000

def z130 : W := mkw 0x0009480264007840 0x0000129004c800f0 0xe01ff803fc007c77 0xdbc03ff007f800f8

def z131 : W := mkw 0xa78217b488fe078e 0x0d4f042f6911fc0f 0x078007fc00fe0388 0x240f000ff801fc07

def z132 : W := mkw 0x22895b36ecfe7fce 0x0c4512b66dd9fcff 0x6680ff1ffcfe7ffd 0xbccd01fe3ff9fcff

def z133 : W := mkw 0x22801b100c640e4a 0x044500362018c81c 0x66003f001ce01c21 0x10cc007e0039c038

def z134 : W := mkw 0xf7c6369000000000 0x23ef8c6d20000000 0xe71f3fe00000003b 0xe3ce3e7fc0000000

def z135 : W := mkw 0x8502048000000000 0x010a040900000000 0x8607070000000021 0x030c0e0e00000000

def z136 : W := mkw 0xf7c0000000000000 0x03ef800000000000 0xe600000000000001 0x03cc000000000000

def z137 : W := mkw 0x000049042c662eca 0x040000920858cc5d 0x0080c01c3ce67fdc 0xb40101803879ccff

def z138 : W := mkw 0x0000000088d50000 0x000000000111aa00 0x0000000000ff8000 0x040000000001ff00

def z139 : W := mkw 0xfff6ffddbef72eca 0x27ffedffbb7dee5d 0xffffffffffffffff 0xffffffffffffffff

def z140 : W := mkw 0xa7e216d888d50000 0x214fc42db111aa00 0x07e007fc00ff8008 0x240fc00ff801ff00

def z141 : W := mkw 0xf7c636919ad50000 0x23ef8c6d2335aa00 0xffe73f03ffff806f 0x9fffce7e07ffff00

def z142 : W := mkw 0x0838c86e250ae9e1 0x00107190dc4a15d3 0x79f8f8fe3f1fffff 0xfcf3f1f1fc7e3fff

def z143 : W := mkw 0x7a94fa153f4628f2 0x16f529f42a7e8c51 0x7880f81c3f060004 0x00f101f0387e0c00

def z144 : W := mkw 0xa78b17b6c8fe578e 0x0d4f162f6d91fcaf 0x879f07ffc0fe7ffb 0xff0f3e0fff81fcff

def z145 : W := mkw 0x0000121000000000 0x0000002420000000 0x0000ff1c00000030 0x200001fe38000000

def z146 : W := mkw 0x0830804800000000 0x0010610090000000 0x19f8c0fc0000001e 0xe033f181f8000000

def z147 : W := mkw 0x0000400420022080 0x0000008008400441 0x19e0c01e231fe3de 0xac33c1803c463fc7

def z148 : W := mkw 0x0838806a00084100 0x00107100d4001082 0x19f8c0fe001863de 0xec33f181fc0030c7

def z149 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6680ff1c3ce6038c 0x24cd01fe3879cc07

def z150 : W := mkw 0x72c000019ad50000 0x02e580000335aa00 0x78e00003ffff8044 0x1cf1c00007ffff00

def z151 : W := mkw 0x8502048000000000 0x010a040900000000 0x871f07e00000003b 0xe30e3e0fc0000000

def z152 : W := mkw 0x856204c800000000 0x210ac40990000000 0x016000e000000000 0x0002c001c0000000

def z153 : W := mkw 0x5874a04800000000 0x22b0e94090000000 0x1860000000000000 0x0030c00000000000

def z154 : W := mkw 0x0000000000000000 0x0000000000000000 0x801f000000000033 0xc3003e0000000000

def z155 : W := mkw 0xf7c0000080900000 0x03ef800001012000 0xffe00003c0f8004f 0x9fffc0000781f000

def z156 : W := mkw 0xd540000192910000 0x03aa800003252200 0x99600003c3198002 0x0b32c00007863300

def z157 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x66003f003ce67fe1 0x14cc007e0079ccff

def z158 : W := mkw 0x0834b25800000000 0x20106964b0000000 0x0000f81c00000000 0x000001f038000000

def z159 : W := mkw 0x0000000000000000 0x0000000000000000 0x01e00000001f8008 0x0403c00000003f00

def z160 : W := mkw 0xf7e0006d9adf8181 0x03efc000db35bf03 0xffe000ffffff83cf 0xbfffc001ffffff07

def z161 : W := mkw 0x2280000008440000 0x0045000000108800 0x668000003ce6004d 0x94cd00000079cc00

def z162 : W := mkw 0xdd76a4c800000000 0x23baed4990000000 0x99ffc0fc0000001e 0xe333ff81f8000000

def z163 : W := mkw 0xf7cb05a2c0b8570c 0x0bef960b458170ae 0xffff07e3c0f87fff 0xfffffe0fc781f0ff

def z164 : W := mkw 0x581dfb1777227efa 0x16b03bf62eee44fd 0xf81fff1fff007ff7 0xfbf03ffe3ffe00ff

def z165 : W := mkw 0x5814a00000000000 0x02b0294000000000 0xf81ff80000000037 0xc3f03ff000000000

def z166 : W := mkw 0x2280121000000000 0x0045002420000000 0x6080f81c00000004 0x00c101f038000000

def z167 : W := mkw 0x0830c04c2102a0a1 0x0010618098420541 0x19f8c0fc2307801e 0xe033f181f8460f00

def z168 : W := mkw 0x583da06b5308d131 0x12b07b40d6a611a2 0x997f00e3c3198002 0x4b32fe01c7863300

def z169 : W := mkw 0xffdde803ffd57870 0x13ffbbd007ffaaf0 0xfffff803fffffc7f 0xdffffff007fffff8

def z170 : W := mkw 0x0830c04c2102a0a1 0x0010618098420541 0x18e0c01c23078004 0x0031c18038460f00

def z171 : W := mkw 0x8500000080900000 0x010a000001012000 0x81000003c0180002 0x0b02000007803000

def z172 : W := mkw 0x228048002c442840 0x0045009000588850 0x6680f8003ce67c7d 0x94cd01f00079ccf8

def z173 : W := mkw 0x22805b102c642e4a 0x044500b62058c85c 0x6600ff003ce07c75 0x90cc01fe0079c0f8

def z174 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z175 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xf81ff8ffff007ff7 0xfbf03ff1fffe00ff

def z176 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x871f07e3c0f81c23 0x5b0e3e0fc781f038

def z177 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xf8073803ff001c67 0x9bf00e7007fe0038

def z178 : W := mkw 0xfff6fed824002840 0x23ffedfdb0480050 0xfffffffc3c007c7f 0xf3fffffff87800f8

def z179 : W := mkw 0x2280121000000000 0x0045002420000000 0x0680071c00000008 0x200d000e38000000

def z180 : W := mkw 0xfff6b6d992910000 0x23ffed6db3252200 0xffffffffc319803f 0xebffffffff863300

def z181 : W := mkw 0xf7c52801ded51850 0x13ef8a5003bdaa30 0xffe73803ffff9c6f 0x9fffce7007ffff38

def z182 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xe01ff801dc007c31 0x53c03ff003b800f8

def z183 : W := mkw 0x850b4da6ecfe7fce 0x0d0a169b4dd9fcff 0x871f07e3fcfe7ffb 0xff0e3e0fc7f9fcff

def z184 : W := mkw 0xf7cb05a3dafd570c 0x0bef960b47b5faae 0xffff07e3ffffffff 0xfffffe0fc7ffffff

def z185 : W := mkw 0x000000019ad50000 0x000000000335aa00 0x19e00003ffff804e 0x9c33c00007ffff00

def z186 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x1978c0fe0319e392 0x6832f181fc0633c7

def z187 : W := mkw 0x2ab0925800000000 0x00556124b0000000 0x7ff8fffc0000003f 0xe0fff1fff8000000

def z188 : W := mkw 0xdd3fedeff7bafffd 0x1bba7fdbdfef75ff 0xffffffffffffffff 0xffffffffffffffff

def z189 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x19f8c0fe231f8006 0x4833f181fc463f00

def z190 : W := mkw 0x7ad4e8013f452870 0x12f5a9d0027e8a50 0x78e0f8003f078004 0x00f1c1f0007e0f00

def z191 : W := mkw 0x0838c06fbbdfe1a1 0x00107180df77bfc3 0x19f8c0ffffffe3de 0xfc33f181ffffffc7

def z192 : W := mkw 0x000305804020160c 0x0800060b0080402c 0x0007070000001c20 0x00000e0e00000038

def z193 : W := mkw 0x0814e80025002870 0x101029d0004a0050 0x0000f80000000000 0x000001f000000000

def z194 : W := mkw 0x581de807770278f0 0x12b03bd00eee04f1 0xf89ff81fff067fff 0xfff13ff03ffe0cff

def z195 : W := mkw 0x0000400420022080 0x0000008008400441 0x00000000200663c0 0x0400000000400cc7

def z196 : W := mkw 0x85030480c0901004 0x090a060901812020 0x80070001c0000000 0x03000e0003800000

def z197 : W := mkw 0xa78b05a2c8fc570c 0x094f160b4591f8ae 0xe79f07e3fcfe7fff 0xffcf3e0fc7f9fcff

def z198 : W := mkw 0x081de80265007870 0x10103bd004ca00f0 0x001ff80000007c30 0x40003ff0000000f8

def z199 : W := mkw 0x22805a142c4628c2 0x044500b428588c51 0x6080f81c3c067c75 0x90c101f038780cf8

def z200 : W := mkw 0x22801b140c660eca 0x044500362818cc1d 0x66803f1c1ce61fa9 0x34cd007e3839cc3f

def z201 : W := mkw 0xffd6b69000000000 0x23ffad6d20000000 0xfe1fff0000000037 0xc3fc3ffe00000000

def z202 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf9fff803ff1ffc7f 0xdff3fff007fe3ff8

def z203 : W := mkw 0x7af6b6d800000000 0x22f5ed6db0000000 0x78fffffc00000034 0x60f1fffff8000000

def z204 : W := mkw 0xffffb7fac0b8570c 0x2bffff6ff58170ae 0xffffffffc0f87fff 0xffffffffff81f0ff

def z205 : W := mkw 0xf7c636919ad50000 0x23ef8c6d2335aa00 0xe6073f01dce00021 0x13cc0e7e03b9c000

def z206 : W := mkw 0xf7c84027bbdfe1a1 0x03ef90804f77bfc3 0xffe00003ffffe3cf 0x9fffc00007ffffc7

def z207 : W := mkw 0x0009000240005000 0x00001200048000a0 0x00000003c0007c40 0x18000000078000f8

def z208 : W := mkw 0x5815e80177003870 0x12b02bd002ee0070 0xf807f801ff001c25 0x13f00ff003fe0038

def z209 : W := mkw 0x00084026210ae1a1 0x000010804c4215c3 0x0000000000006380 0x00000000000000c7

def z210 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0x9fff07fc0000000a 0x633ffe0ff8000000

def z211 : W := mkw 0xffffb6db53005030 0x33ffff6db6a600a0 0xffffffffc300003f 0xebffffffff860000

def z212 : W := mkw 0xd540000192910000 0x03aa800003252200 0x9f600003c3f9804b 0x9f3ec0000787f300

def z213 : W := mkw 0xdd5de803f7917870 0x13babbd007ef22f0 0xf97ff803ff19fc77 0xdbf2fff007fe33f8

def z214 : W := mkw 0xdd5da003d3915030 0x13babb4007a722a0 0x997f0003c3198002 0x4b32fe0007863300

def z215 : W := mkw 0xaffad6fe210ae1a1 0x215ff5adfc4215c3 0x1ff8c7fe231fe3de 0xec3ff18ffc463fc7

def z216 : W := mkw 0x581de82377087970 0x12b03bd046ee10f2 0xf91ff8e3ff187fff 0xfff23ff1c7fe30ff

def z217 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x7fe0ff1e3fffffff 0xbcffc1fe3c7fffff

def z218 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffe231f807f 0xeffffffffc463f00

def z219 : W := mkw 0x000001040866068a 0x040000020810cc0d 0x0000000000e60380 0x040000000001cc07

def z220 : W := mkw 0x583de86b7708f971 0x12b07bd0d6ee11f2 0xf97ff8e3ff19fc77 0xdbf2fff1c7fe33f8

def z221 : W := mkw 0x0000000000000000 0x0000000000000000 0x010000020018004a 0x8c02000004003000

def z222 : W := mkw 0x500000019ad50000 0x02a000000335aa00 0xf8000003ffff8047 0x9ff0000007ffff00

def z223 : W := mkw 0x2280010008640608 0x004500020010c80c 0x668007003ce67ffd 0xb4cd000e0079ccff

def z224 : W := mkw 0x22805a142c4628c2 0x044500b428588c51 0x6680f81c3ce6004d 0x94cd01f03879cc00

def z225 : W := mkw 0x72c4321000000000 0x22e5886420000000 0x6000380000000000 0x00c0007000000000

def z226 : W := mkw 0x083fb7fa4028570c 0x28107f6ff48050ae 0x001ffffc00007fb0 0x60003ffff80000ff

def z227 : W := mkw 0xfffde86fffdff9f1 0x13fffbd0dfffbff3 0xfffff8ffffffffff 0xfffffff1ffffffff

def z228 : W := mkw 0xa7e0006c88df8181 0x014fc000d911bf03 0x07e000fc00ff8388 0x240fc001f801ff07

def z229 : W := mkw 0x85090122c0b8570c 0x090a1202458170ae 0x87000003c0f87fcb 0x9f0e00000781f0ff

def z230 : W := mkw 0x0830804801008021 0x0010610090020100 0x1860000003018000 0x0030c00000060300

def z231 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6600ff1c1ce07fb1 0x30cc01fe3839c0ff

def z232 : W := mkw 0x0830c04c20022080 0x0010618098400441 0x19f8c0fc200663de 0xe433f181f8400cc7

def z233 : W := mkw 0x850b45a6e0ba778c 0x090a168b4dc174ef 0x879fc7ffe0fe7fff 0xff0f3f8fffc1fcff

def z234 : W := mkw 0x0008000200004000 0x0000100004000080 0x0018000200006052 0xc8003000040000c0

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000002231f8040 0x0c00000004463f00

def z236 : W := mkw 0x0000000008440000 0x0000000000108800 0x000000003ce60040 0x140000000079cc00

def z237 : W := mkw 0x5000000112000000 0x02a0000002240000 0xf8000003ff000047 0x9bf0000007fe0000

def z238 : W := mkw 0xfff6b6d912000000 0x23ffed6db2240000 0xffffffffff00007f 0xfbfffffffffe0000

def z239 : W := mkw 0x0818c80225006860 0x00103190044a00d0 0x7818f8023f007c77 0xd8f031f0047e00f8

def z240 : W := mkw 0x850b05a24028570c 0x090a160b448050ae 0x871f07e000007fbb 0xe30e3e0fc00000ff

def z241 : W := mkw 0x0830c04c2102a0a1 0x0010618098420541 0x0000c01c00000000 0x0000018038000000

def z242 : W := mkw 0x0838806a0108c121 0x00107100d4021182 0x197800e203198002 0x4832f001c4063300

def z243 : W := mkw 0xfffffeff770af9f1 0x33fffffdfeee15f3 0xffffffffff1fffff 0xfffffffffffe3fff

def z244 : W := mkw 0xffdde803ffd57870 0x13ffbbd007ffaaf0 0xfe1ff803ffe07c77 0xdbfc3ff007ffc0f8

def z245 : W := mkw 0x7af4fb5c2c662eca 0x26f5e9f6b858cc5d 0x7ee0ff1c3ce67ffd 0xb4fdc1fe3879ccff

def z246 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x9fff07e3e3ffffff 0xff3ffe0fc7c7ffff

def z247 : W := mkw 0xfff080499ad50000 0x03ffe1009335aa00 0xfff8c0ffffff805f 0xfffff181ffffff00

def z248 : W := mkw 0x0819c80377007870 0x1010339006ee00f0 0x1818c003ff007c56 0xd830318007fe00f8

def z249 : W := mkw 0x7af8c06f3b4fe1a1 0x02f5f180de769fc3 0x79f8c0fe3f1fe3de 0xecf3f181fc7e3fc7

def z250 : W := mkw 0x2ab8d27e210ae1a1 0x005571a4fc4215c3 0x7ff8fffe231fe3ff 0xecfff1fffc463fc7

def z251 : W := mkw 0x000800220108c121 0x0000100044021182 0x0000000203198000 0x0800000004063300

def z252 : W := mkw 0x00084026200a6180 0x000010804c4014c3 0x0198c0fe201e63de 0xec033181fc403cc7

def z253 : W := mkw 0x0020406c200aa181 0x00004080d8401543 0x01e0c0fc201fe3dc 0xa403c181f8403fc7

def z254 : W := mkw 0x850b05a3dafd570c 0x090a160b47b5faae 0x871f07e3fffffffb 0xff0e3e0fc7ffffff

def z255 : W := mkw 0x228013100864060a 0x044500262010c80c 0x0600070000e00000 0x000c000e0001c000

def z256 : W := mkw 0x583de84b77007870 0x12b07bd096ee00f0 0xf9fff8ffff007c7f 0xfbf3fff1fffe00f8

def z257 : W := mkw 0xfff6b7dc0866068a 0x27ffed6fb810cc0d 0xfffffffc00e603bf 0xe7fffffff801cc07

def z258 : W := mkw 0x22e0125800000000 0x2045c024b0000000 0x00e0001c00000000 0x0001c00038000000

def z259 : W := mkw 0xa7cb05a2c8fd570c 0x094f960b4591faae 0x87ff07e3c0fffffb 0xff0ffe0fc781ffff

def z260 : W := mkw 0x583ffedb77007870 0x32b07ffdb6ee00f0 0xf81fffffff007c77 0xfbf03ffffffe00f8

def z261 : W := mkw 0x72c000011a450000 0x02e5800002348a00 0x7ee000003fe7804d 0x94fdc000007fcf00

def z262 : W := mkw 0x7abdfb7f7f6efffb 0x16f57bf6fefeddff 0xffffffffffffffff 0xffffffffffffffff

def z263 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6680ff1c3ce61c25 0x10cd01fe3879cc38

def z264 : W := mkw 0x8502058000200608 0x010a040b0000400c 0x871f07e000e07ffb 0xf70e3e0fc001c0ff

def z265 : W := mkw 0x0839c06e610af1a1 0x00107380dcc215e3 0x99ffc0ffe31fffff 0xff33ff81ffc63fff

def z266 : W := mkw 0xa7c05b14acf72eca 0x054f80b62959ee5d 0x67e0ff1c3cfffffd 0xb4cfc1fe3879ffff

def z267 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0x7800f803ff007c44 0x18f001f007fe00f8

def z268 : W := mkw 0xfffeb6fa00084100 0x23fffd6df4001082 0xfffffffe001863ff 0xeffffffffc0030c7

def z269 : W := mkw 0x0000010000200608 0x000000020000400c 0x0600070000e07ff9 0xb40c000e0001c0ff

def z270 : W := mkw 0x228013140866068a 0x044500262810cc0d 0x6680071c3ce603cd 0xb4cd000e3879cc07

def z271 : W := mkw 0x0009480377007870 0x1000129006ee00f0 0x00000003ff007c40 0x1800000007fe00f8

def z272 : W := mkw 0x0830804800000000 0x0010610090000000 0x19f8c0fe231f805e 0xec33f181fc463f00

def z273 : W := mkw 0x5000000112000000 0x02a0000002240000 0x98000003c3000002 0x0b30000007860000

def z274 : W := mkw 0x0009000353005030 0x1000120006a600a0 0x00000003c3000000 0x0800000007860000

def z275 : W := mkw 0x00004905bef72eca 0x040000920b7dee5d 0x00000003ffffffc0 0x1c00000007ffffff

def z276 : W := mkw 0x0000410420222688 0x000000820840444d 0x0680c71c20e67ffd 0xb40d018e3841ccff

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x600000003c000045 0x90c0000000780000

def z278 : W := mkw 0xdd1feca3f7987974 0x1bba3fd947ef30f2 0xf91ff8e3ff187c77 0xdbf23ff1c7fe30f8

def z279 : W := mkw 0x2280000000000000 0x0045000000000000 0x668000000000000d 0x80cd000000000000

def z280 : W := mkw 0xf7c012119ad50000 0x03ef80242335aa00 0xffe0ff1fffff807f 0xbfffc1fe3fffff00

def z281 : W := mkw 0x7a9de8037f447870 0x12f53bd006fe88f0 0xfe9ff803ffe67c7f 0xdffd3ff007ffccf8

def z282 : W := mkw 0xf7c01b119ef50e4a 0x07ef8036233dea1c 0xe6003f01dce01c21 0x13cc007e03b9c038

def z283 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xff600003dff98003 0x1bfec00007bff300

def z284 : W := mkw 0x0838806a0108c121 0x00107100d4021182 0x19f8c0fe0319801e 0xe833f181fc063300

def z285 : W := mkw 0x083de86e650af9f1 0x10107bd0dcca15f3 0x001ff8fc00007fb0 0x60003ff1f80000ff

def z286 : W := mkw 0x0000010000200608 0x000000020000400c 0x0000000000e07fc0 0x140000000001c0ff

def z287 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x0680ff1c00e67fb8 0x240d01fe3801ccff

def z288 : W := mkw 0x000049042c662eca 0x040000920858cc5d 0x060007003ce67ff9 0xb40c000e0079ccff

def z289 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000063d8 0xa4000000000000c7

def z290 : W := mkw 0xffd8c003bbd56020 0x03ffb1800777aac0 0xfff8c003ffffe05f 0xdffff18007ffffc0

def z291 : W := mkw 0x8508002280984100 0x010a100045013082 0x871800e3c0f863db 0xff0e3001c781f0c7

def z292 : W := mkw 0x0009000240005000 0x00001200048000a0 0x001f000000007c30 0x40003e00000000f8

def z293 : W := mkw 0xffd4a0019ad50000 0x03ffa9400335aa00 0xfffff803ffff807f 0xdffffff007ffff00

def z294 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0x981ff803c3007c32 0x4b303ff0078600f8

def z295 : W := mkw 0xd54000019ad50000 0x03aa80000335aa00 0x99600003ffff8042 0x1f32c00007ffff00

def z296 : W := mkw 0x0000490424222eca 0x040000920848445d 0x0000000000007f80 0x00000000000000ff

def z297 : W := mkw 0x00094827770af9f1 0x100012904eee15f3 0x00000003ff1fffc0 0x1c00000007fe3fff

def z298 : W := mkw 0x850000019ad50000 0x010a00000335aa00 0x87000003ffff804b 0x9f0e000007ffff00

def z299 : W := mkw 0xf7c01b119ef50e4a 0x07ef8036233dea1c 0xffe03f03ffff9c6f 0x9fffc07e07ffff38

def z300 : W := mkw 0x0818c00221006020 0x00103180044200c0 0x1818c00223006056 0xc8303180044600c0

def z301 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xffe00001dce0000f 0x93ffc00003b9c000

def z302 : W := mkw 0xa7825f942c662eca 0x054f04bf2858cc5d 0xe79ffffc3ce67fff 0xf7cf3ffff879ccff

def z303 : W := mkw 0xf7c63f900c640e4a 0x27ef8c7f2018c81c 0xe6073f001ce01c21 0x13cc0e7e0039c038

def z304 : W := mkw 0x22801b100c640e4a 0x044500362018c81c 0x66003f001ce07ff9 0xb4cc007e0039c0ff

def z305 : W := mkw 0xfff0804800000000 0x03ffe10090000000 0xfff8c0fc0000001f 0xe3fff181f8000000

def z306 : W := mkw 0x7af4fa5c2c4628c2 0x26f5e9f4b8588c51 0x78e0f81c3c060004 0x00f1c1f038780c00

def z307 : W := mkw 0x00094923f7b87f7c 0x1800129247ef70fe 0x00000003fff87fc0 0x1c00000007fff0ff

def z308 : W := mkw 0x228053142866268a 0x044500a62850cc4d 0x0680c71c20e663dc 0xa40d018e3841ccc7

def z309 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000007c71 0x90000000000000f8

def z310 : W := mkw 0x850b04a2c0985104 0x090a1609458130a2 0x811f00e3c0187c73 0xdb023e01c78030f8

def z311 : W := mkw 0x2ab0da5c2d46a8e3 0x045561b4b85a8d51 0x78e0f81c3f078004 0x00f1c1f0387e0f00

def z312 : W := mkw 0xfff6bfd80c640e4a 0x27ffed7fb018c81c 0xfffffffc1ce01c3f 0xf3fffffff839c038

def z313 : W := mkw 0xffffb7fa4028570c 0x2bffff6ff48050ae 0xfffffffc00007fbf 0xe3fffffff80000ff

def z314 : W := mkw 0x0006369000000000 0x20000c6d20000000 0x00073f0000000020 0x00000e7e00000000

def z315 : W := mkw 0xfffef6da21006020 0x23fffdedb44200c0 0xfffffffe2300607f 0xebfffffffc4600c0

def z316 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x1818c0fe230063d6 0xe8303181fc4600c7

def z317 : W := mkw 0x5834a04800000000 0x02b0694090000000 0xf9fff8fc0000003f 0xe3f3fff1f8000000

def z318 : W := mkw 0xa7e216d800000000 0x214fc42db0000000 0x67e0fffc0000003d 0xa0cfc1fff8000000

def z319 : W := mkw 0x0000480024002840 0x0000009000480050 0x6000f8003c000004 0x00c001f000780000

def z320 : W := mkw 0x081de80265007870 0x10103bd004ca00f0 0x601ff8003c007c75 0xd0c03ff0007800f8

def z321 : W := mkw 0xffd4e801bfd52870 0x13ffa9d0037faa50 0xffe0f803ffff804f 0x9fffc1f007ffff00

def z322 : W := mkw 0x850b048240005000 0x010a1609048000a0 0x871f07e3c0007c7b 0xfb0e3e0fc78000f8

def z323 : W := mkw 0x5000000112000000 0x02a0000002240000 0xf9e00003ff1f804f 0x9ff3c00007fe3f00

def z324 : W := mkw 0xfffef6fe210ae1a1 0x23fffdedfc4215c3 0xfffffffc000063bf 0xe3fffffff80000c7

def z325 : W := mkw 0x0838806a0108c121 0x00107100d4021182 0x001800e000000000 0x40003001c0000000

def z326 : W := mkw 0xfff6f6dc2102a0a1 0x23ffededb8420541 0xfffffffc2307803f 0xe3fffffff8460f00

def z327 : W := mkw 0x000040042102a0a1 0x0000008008420541 0x0000000023078000 0x0000000000460f00

def z328 : W := mkw 0x5815a80156001850 0x12b02b5002ac0030 0xf81ff801dc001c37 0xd3f03ff003b80038

def z329 : W := mkw 0x8502048000000000 0x010a040900000000 0x811f00e000000002 0x43023e01c0000000

def z330 : W := mkw 0xdd78c06fb39be1a1 0x03baf180df6737c3 0x99f8c0ffe31fe3de 0xef33f181ffc63fc7

def z331 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x070007e3c0f87fc8 0x3c0e000fc781f0ff

def z332 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xfee00001ffe78005 0x13fdc00003ffcf00

def z333 : W := mkw 0x728000011a440000 0x02e5000002348800 0xfe800003ffe6004f 0x9ffd000007ffcc00

def z334 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x071f07e000f87fb8 0x640e3e0fc001f0ff

def z335 : W := mkw 0x0838c04a21006020 0x00107180944200c0 0x19f8c0fe2300605e 0xe833f181fc4600c0

def z336 : W := mkw 0xfffffedbffd57870 0x33fffffdb7ffaaf0 0xfffffffffffffc7f 0xfffffffffffffff8

def z337 : W := mkw 0xd540000192910000 0x03aa800003252200 0x99e00003e31f804e 0x8f33c00007c63f00

def z338 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x19fffffc0000003e 0xe033fffff8000000

def z339 : W := mkw 0xa7c0000088d50000 0x014f80000111aa00 0x0600000000e00000 0x000c00000001c000

def z340 : W := mkw 0xd500000192900000 0x03aa000003252000 0xff000003fff8004f 0x9ffe000007fff000

def z341 : W := mkw 0x500d280356005850 0x12a01a5006ac00b0 0xe01f3803dc007c73 0xdbc03e7007b800f8

def z342 : W := mkw 0xf7c30581daf5160c 0x0bef860b03b5ea2c 0xffe70703ffff9c6f 0x9fffce0e07ffff38

def z343 : W := mkw 0x0818c006210260a0 0x001031800c4204c1 0x1898c01e230663de 0xec3131803c460cc7

def z344 : W := mkw 0x2ab6ffdc2c662eca 0x24556dffb858cc5d 0x669ffffc3ce67ffd 0xf4cd3ffff879ccff

def z345 : W := mkw 0x2280121000000000 0x0045002420000000 0x66003f0000000021 0x00cc007e00000000

def z346 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xe7e00001dcff8009 0x17cfc00003b9ff00

def z347 : W := mkw 0x2ab0db5c2d66aeeb 0x045561b6b85acd5d 0x7ee0ff1c3fe7fffd 0xb4fdc1fe387fcfff

def z348 : W := mkw 0xfff7b7d8c0b0160c 0x2bffef6fb181602c 0xfffffffdc0e01c3f 0xf3fffffffb81c038

def z349 : W := mkw 0x0028006e000ac181 0x00005000dc001583 0x01f800fe001fe3da 0xec03f001fc003fc7

def z350 : W := mkw 0x7af4b25800000000 0x22f5e964b0000000 0xf8fff81c00000037 0xc3f1fff038000000

def z351 : W := mkw 0xffd4a00000000000 0x03ffa94000000000 0xfffff8000000003f 0xc3fffff000000000

def z352 : W := mkw 0x0830804800000000 0x0010610090000000 0x18e0c01c00000004 0x0031c18038000000

def z353 : W := mkw 0x0000480024002840 0x0000009000480050 0x0000f80000007c30 0x000001f0000000f8

def z354 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x871f07e3c0f8038a 0x6f0e3e0fc781f007

def z355 : W := mkw 0x850b0582c0b0560c 0x090a160b058160ac 0x861f0703c0e07c73 0xdb0c3e0e0781c0f8

def z356 : W := mkw 0x22885b362c6e6fca 0x044510b66c58dcdf 0x6798fffe3cfe7fff 0xfccf31fffc79fcff

def z357 : W := mkw 0x7a9dfa1377007870 0x12f53bf426ee00f0 0xfe9fff1fff007c7f 0xfbfd3ffe3ffe00f8

def z358 : W := mkw 0x00094926ecfe7fce 0x0c0012924dd9fcff 0x00000003fcfe7fc0 0x1c00000007f9fcff

def z359 : W := mkw 0xd5072d81d6b01e5c 0x1baa0e5b03ad603c 0xe6073f01dce01c21 0x13cc0e7e03b9c038

def z360 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x18e0c01e231fe3c4 0x0c31c1803c463fc7

def z361 : W := mkw 0xf7e216d99ad50000 0x23efc42db335aa00 0xffe007ffffff804f 0xbfffc00fffffff00

def z362 : W := mkw 0x22805a142c4628c2 0x044500b428588c51 0x6680ff1c3c06003d 0xa0cd01fe38780c00

def z363 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0x7fe000003fff800c 0x04ffc000007fff00

def z364 : W := mkw 0x000b05a24028570c 0x0800160b448050ae 0x801f07e3c0007ff3 0xfb003e0fc78000ff

def z365 : W := mkw 0xf7c0000088d50000 0x03ef80000111aa00 0xffe0000000ff800f 0x87ffc0000001ff00

def z366 : W := mkw 0x2280000008440000 0x0045000000108800 0x7fe000023fff804f 0x9cffc000047fff00

def z367 : W := mkw 0x850a05a280b8470c 0x090a140b4501708e 0x071807e200f863da 0xec0e300fc401f0c7

def z368 : W := mkw 0x0002048000000000 0x0000040900000000 0x001f07e000000030 0x60003e0fc0000000

def z369 : W := mkw 0xafbbdffeedfeffef 0x0d5f77bffddbfdff 0xffffffffffffffff 0xffffffffffffffff

def z370 : W := mkw 0x85090002c0905000 0x010a1200058120a0 0x871f0003c0f87c7b 0xdf0e3e000781f0f8

def z371 : W := mkw 0x581de00373007030 0x12b03bc006e600e0 0x981fc003e3006056 0xcb303f8007c600c0

def z372 : W := mkw 0x0818c00221006020 0x00103180044200c0 0x0018c00000006010 0x40003180000000c0

def z373 : W := mkw 0xf7e636d800000000 0x23efcc6db0000000 0xe7e73ffc00000029 0x23cfce7ff8000000

def z374 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0x981f0003ff007c42 0x5b303e0007fe00f8

def z375 : W := mkw 0xfff8db7fbfffefeb 0x07fff1b6ff7fffdf 0xfff8ffffffffffff 0xfffff1ffffffffff

def z376 : W := mkw 0x5818c00333006020 0x02b03180066600c0 0xf818c003ff006057 0xdbf0318007fe00c0

def z377 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xfffffffddce0003f 0xf3fffffffbb9c000

def z378 : W := mkw 0xfff6b6d808440000 0x23ffed6db0108800 0xfffffffc3ce6007f 0xf7fffffff879cc00

def z379 : W := mkw 0x0836a4c800000000 0x20106d4990000000 0x001f00e000000000 0x40003e01c0000000

def z380 : W := mkw 0x8d1feda2e5b87f7c 0x191a3fdb45cb70fe 0x871fffe3c0f87ffb 0xff0e3fffc781f0ff

def z381 : W := mkw 0x8502048080900000 0x010a040901012000 0x871f07e3c0f8007b 0xff0e3e0fc781f000

def z382 : W := mkw 0x228013140866068a 0x044500262810cc0d 0x0680071c00e67ff9 0xb40d000e3801ccff

def z383 : W := mkw 0x000000011a450000 0x0000000002348a00 0x000000003f078000 0x00000000007e0f00

def z384 : W := mkw 0xfffefffe2d6eefeb 0x27fffdfffc5adddf 0xfffffffe3fffffff 0xfffffffffc7fffff

def z385 : W := mkw 0x0838c06a2108e121 0x00107180d44211c2 0x1978c0e22319e056 0xc832f181c44633c0

def z386 : W := mkw 0x8d3bc4eee19af1a5 0x091a7789ddc335e3 0x99ffc0ffe31fe3de 0xef33ff81ffc63fc7

def z387 : W := mkw 0x00090122c0b8570c 0x08001202458170ae 0x06000703c0f87ff9 0xbc0c000e0781f0ff

def z388 : W := mkw 0x228000019ad50000 0x004500000335aa00 0x66800003ffff804d 0x9ccd000007ffff00

def z389 : W := mkw 0x0810800000000000 0x0010210000000000 0x1818c00000000016 0xc030318000000000

def z390 : W := mkw 0x852205ec80ba878d 0x090a440bd901750f 0x07e007fc00ff8388 0x240fc00ff801ff07

def z391 : W := mkw 0x583de84f7702f8f1 0x12b07bd09eee05f1 0xf8fff81fff07fc77 0xdbf1fff03ffe0ff8

def z392 : W := mkw 0xa7835f94ecf63ece 0x0d4f06bf29d9ec7d 0xe687ff1dfce67ffd 0xb7cd0ffe3bf9ccff

def z393 : W := mkw 0x0838c16e212ae7a9 0x00107182dc4255cf 0x1ff8c7fe23ffffff 0xfc3ff18ffc47ffff

def z394 : W := mkw 0x850b4da3f7b87f7c 0x190a169b47ef70fe 0x871f07e3fff87ffb 0xff0e3e0fc7fff0ff

def z395 : W := mkw 0x22801b100c640e4a 0x044500362018c81c 0x6680ff1c1ce01c3d 0xb0cd01fe3839c038

def z396 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xf9e00003ff1f8006 0x0bf3c00007fe3f00

def z397 : W := mkw 0xf7c73e9156001850 0x33ef8e7d22ac0030 0xe6073f01dc001c21 0x13cc0e7e03b80038

def z398 : W := mkw 0x852b05eec0bad78d 0x090a560bdd8175af 0x87ff07ffc0fffffb 0xff0ffe0fff81ffff

def z399 : W := mkw 0xdd1fa5a3d3b8573c 0x1bba3f4b47a770ae 0x9f1f07e3c3f87ffb 0xff3e3e0fc787f0ff

def z400 : W := mkw 0x0818c026210ae1a1 0x001031804c4215c3 0x1818c002231fe3d6 0xcc30318004463fc7

def z401 : W := mkw 0x000049042c662eca 0x040000920858cc5d 0x6000f8003ce67ff5 0x94c001f00079ccff

def z402 : W := mkw 0x85030580c0b0160c 0x090a060b0181602c 0x871f07e1c0e01c3b 0xf30e3e0fc381c038

def z403 : W := mkw 0x083de86e650af9f1 0x10107bd0dcca15f3 0x19fff8fe231ffffe 0xec33fff1fc463fff

def z404 : W := mkw 0xf7cf37b2c0b8570c 0x2bef9e6f658170ae 0xe71f3fe3c0f87ffb 0xffce3e7fc781f0ff

def z405 : W := mkw 0xa7c0000088d50000 0x014f80000111aa00 0x87e00003c0ff804b 0x9f0fc0000781ff00

def z406 : W := mkw 0xa7c000019ad50000 0x014f80000335aa00 0x07e00003ffff8048 0x1c0fc00007ffff00

def z407 : W := mkw 0x581da80357005870 0x12b03b5006ae00b0 0xf81f3803df001c23 0x5bf03e7007be0038

def z408 : W := mkw 0x7a94b21000000000 0x02f5296420000000 0xfe9fff1c0000003f 0xe3fd3ffe38000000

def z409 : W := mkw 0x00001b1004200e4a 0x040000362008401c 0x00003f0000001c20 0x0000007e00000038

def z410 : W := mkw 0x581ce80337006870 0x12b039d0066e00d0 0x7818f8023f006056 0xc8f031f0047e00c0

def z411 : W := mkw 0x583ce86f370ae9f1 0x12b079d0de6e15d3 0x79f8f8fe3f1fe3de 0xecf3f1f1fc7e3fc7

def z412 : W := mkw 0x0009002240085100 0x00001200448010a2 0x811f00e3c0187ffb 0xff023e01c78030ff

def z413 : W := mkw 0x8540000080910000 0x010a800001012200 0x0160000000198000 0x0002c00000003300

def z414 : W := mkw 0xf7c800239add4100 0x03ef90004735ba82 0xfff800e3ffffe3df 0xfffff001c7ffffc7

def z415 : W := mkw 0x000b05a24028570c 0x0800160b448050ae 0x061f07e000e07ff9 0xf40c3e0fc001c0ff

def z416 : W := mkw 0x22c0000008450000 0x0045800000108a00 0x00e0000000078000 0x0001c00000000f00

def z417 : W := mkw 0xf7e216d800000000 0x23efc42db0000000 0xffe007fc0000000f 0xa3ffc00ff8000000

def z418 : W := mkw 0xfffff7fee1baf7ad 0x2bffffeffdc375ef 0xffffffffe3ffffff 0xffffffffffc7ffff

def z419 : W := mkw 0x0000000000000000 0x0000000000000000 0x19e000000000000e 0x8033c00000000000

def z420 : W := mkw 0x850a04a200084100 0x010a140944001082 0x871f07e2001863fb 0xef0e3e0fc40030c7

def z421 : W := mkw 0xaff8c06ea9dfe1a1 0x015ff180dd53bfc3 0x1ff8c0fe23ffe3de 0xec3ff181fc47ffc7

def z422 : W := mkw 0xfff8c06e210ae1a1 0x03fff180dc4215c3 0xfff8c0fe231fe3df 0xeffff181fc463fc7

def z423 : W := mkw 0x72853b115e641e5a 0x16e50a7622bcc83c 0xe6073f01dce01c21 0x13cc0e7e03b9c038

def z424 : W := mkw 0xfff6b6d880900000 0x23ffed6db1012000 0xffffffffc0f8007f 0xffffffffff81f000

def z425 : W := mkw 0x583de06f730af1b1 0x12b07bc0dee615e3 0x99ffc0ffe31fe3de 0xef33ff81ffc63fc7

def z426 : W := mkw 0x5005200152001010 0x12a00a4002a40020 0x80070001c0000000 0x03000e0003800000

def z427 : W := mkw 0x2280521420022080 0x004500a428400441 0x6680ff1c200663fd 0xa4cd01fe38400cc7

def z428 : W := mkw 0x0814a00000000000 0x0010294000000000 0x001ff80000000030 0x40003ff000000000

def z429 : W := mkw 0xd54b04a3d2995104 0x0baa960947a532a2 0x997f00e3c3198002 0x4b32fe01c7863300

def z430 : W := mkw 0xf7c73790c0b0160c 0x2bef8e6f2181602c 0xe6073f01c0e01c21 0x13cc0e7e0381c038

def z431 : W := mkw 0x00084026210ae1a1 0x000010804c4215c3 0x19e00002231fe3ce 0x8c33c00004463fc7

def z432 : W := mkw 0xa7c0000088d50000 0x014f80000111aa00 0x1fe0000223ff804e 0x8c3fc0000447ff00

def z433 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfee7ff1c00000025 0x03fdcffe38000000

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x18e0000023078004 0x0031c00000460f00

def z435 : W := mkw 0x000205a00028070c 0x0800040b4000500e 0x000007e000000380 0x2000000fc0000007

def z436 : W := mkw 0xfff6b6d91a450000 0x23ffed6db2348a00 0xfffffffc3f07803f 0xe3fffffff87e0f00

def z437 : W := mkw 0x5000000112000000 0x02a0000002240000 0xe0000001dc000001 0x13c0000003b80000

def z438 : W := mkw 0xa7e217f880b8070c 0x294fc42ff101700e 0x07e007fc00f80388 0x240fc00ff801f007

def z439 : W := mkw 0xdd76a4c992910000 0x23baed4993252200 0x997f00e3c3198002 0x4b32fe01c7863300

def z440 : W := mkw 0xaff296d800000000 0x215fe52db0000000 0x1ff8c7fc0000001e 0xe03ff18ff8000000

def z441 : W := mkw 0x5814e80137002870 0x12b029d0026e0050 0xf81ff8003f000037 0xc3f03ff0007e0000

def z442 : W := mkw 0x0000400420022080 0x0000008008400441 0x0080c01c20060004 0x0001018038400c00

def z443 : W := mkw 0x0818c02221086120 0x00103180444210c2 0x1918c0e2231863de 0xec323181c44630c7

def z444 : W := mkw 0xf7c204819ad50000 0x03ef84090335aa00 0xffff07e3ffff807f 0xfffffe0fc7ffff00

def z445 : W := mkw 0x581da00240005000 0x02b03b40048000a0 0xf81ff803c0007c77 0xdbf03ff0078000f8

def z446 : W := mkw 0x2280000008440000 0x0045000000108800 0x660000001ce00001 0x10cc00000039c000

def z447 : W := mkw 0x0000080004000840 0x0000001000080010 0x600038001c001c21 0x10c0007000380038

def z448 : W := mkw 0x22a0137c086e878b 0x04454026f810dd0f 0x07e007fc00ff8388 0x240fc00ff801ff07

def z449 : W := mkw 0x000048042c4628c2 0x0400009008588c51 0x000000003c060000 0x0000000000780c00

def z450 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0x7fe0fffc0000000c 0x20ffc1fff8000000

def z451 : W := mkw 0x0001080156001850 0x1000021002ac0030 0x00000001dc001c00 0x1000000003b80038

def z452 : W := mkw 0x0009480377007870 0x1000129006ee00f0 0x6000f803ff007c75 0x98c001f007fe00f8

def z453 : W := mkw 0x0830c04c2102a0a1 0x0010618098420541 0x19e0c01e231f804e 0x8c33c1803c463f00

def z454 : W := mkw 0xfffeb6fa0108c121 0x23fffd6df4021182 0xfffffffe0319803f 0xebfffffffc063300

def z455 : W := mkw 0xf7cb5fb7feff7fce 0x0fef96bf6ffdfeff 0xffffffffffffffff 0xffffffffffffffff

def z456 : W := mkw 0xfff6fedc2c4628c2 0x27ffedfdb8588c51 0xfffffffc3c06003f 0xe3fffffff8780c00

def z457 : W := mkw 0x7af4f25c2102a0a1 0x22f5e9e4b8420541 0x78e0f81c23078004 0x00f1c1f038460f00

def z458 : W := mkw 0x2ab6b6d800000000 0x20556d6db0000000 0x669ffffc0000003d 0xe0cd3ffff8000000

def z459 : W := mkw 0x7a9dfb137f647e7a 0x16f53bf626fec8fc 0xfe1fff03ffe07c77 0xdbfc3ffe07ffc0f8

def z460 : W := mkw 0xdd78806b9399c121 0x03baf100d7273382 0x997800e3c3198002 0x4b32f001c7863300

def z461 : W := mkw 0xf7c6369000000000 0x23ef8c6d20000000 0xffe73f000000002f 0x83ffce7e00000000

def z462 : W := mkw 0x850305a0c0b8170c 0x090a060b4181702e 0x870707e1c0f81fa9 0x370e0e0fc381f03f

def z463 : W := mkw 0x0838c04e2102e0a1 0x001071809c4205c1 0x18f8c01e2307e056 0xc831f1803c460fc0

def z464 : W := mkw 0x7afdfa5b77007870 0x32f5fbf4b6ee00f0 0xf8fff81fff007c77 0xdbf1fff03ffe00f8

def z465 : W := mkw 0x0008012200284708 0x000010024400508e 0x071807e200f87ffb 0xfc0e300fc401f0ff

def z466 : W := mkw 0xf7c0000008440000 0x03ef800000108800 0xffe000003ce6004f 0x97ffc0000079cc00

def z467 : W := mkw 0x2280131000200608 0x004500262000400c 0x6680ff1c00e07ffd 0xb4cd01fe3801c0ff

def z468 : W := mkw 0x0008400221006020 0x00001080044200c0 0x0000000223006040 0x08000000044600c0

def z469 : W := mkw 0x5004280116000850 0x12a00850022c0010 0x600038001c000000 0x00c0007000380000

def z470 : W := mkw 0x583ce06e210ae1a1 0x02b079c0dc4215c3 0xf9fff8fe231fe3ff 0xeff3fff1fc463fc7

def z471 : W := mkw 0x850b04a2c0985104 0x090a1609458130a2 0x811f00e3c01863da 0xef023e01c78030c7

def z472 : W := mkw 0xf7c05b15bef72eca 0x07ef80b62b7dee5d 0xe680ff1dfce67ffd 0xb7cd01fe3bf9ccff

def z473 : W := mkw 0xaff6b6d800000000 0x215fed6db0000000 0x07fffffc00000038 0x600ffffff8000000

def z474 : W := mkw 0xa7c0000000000000 0x014f800000000000 0x07e0000000000008 0x000fc00000000000

def z475 : W := mkw 0x581de803ffd57870 0x12b03bd007ffaaf0 0xf81ff803fffffc77 0xdff03ff007fffff8

def z476 : W := mkw 0x081feda265287f7c 0x18103fdb44ca50fe 0x001fffe000007fb0 0x60003fffc00000ff

def z477 : W := mkw 0xfff6fed937002870 0x33ffedfdb26e0050 0xfffffffc3f00003f 0xe3fffffff87e0000

def z478 : W := mkw 0x00084027bbdfe1a1 0x000010804f77bfc3 0x00000003ffffe3c0 0x1c00000007ffffc7

def z479 : W := mkw 0x228049042c662eca 0x044500920858cc5d 0x668000003ce67fcd 0x94cd00000079ccff

def z480 : W := mkw 0x850205a080b8070c 0x090a040b4101700e 0x070007e000f87ff9 0xb40e000fc001f0ff

def z481 : W := mkw 0xffdda003dbd55030 0x13ffbb4007b7aaa0 0xffff0003ffff804f 0xdffffe0007ffff00

def z482 : W := mkw 0x22805b1424222eca 0x044500b62848445d 0x6680ff1c00007fbd 0xa0cd01fe380000ff

def z483 : W := mkw 0xd540000192910000 0x03aa800003252200 0x80000001c0000000 0x0300000003800000

def z484 : W := mkw 0x8d1bc5a2e1b8772c 0x091a378b45c370ee 0x9f1fc7e3e3f87fff 0xff3e3f8fc7c7f0ff

def z485 : W := mkw 0x0000000000000000 0x0000000000000000 0x1800000223000046 0x8830000004460000

def z486 : W := mkw 0xf7c04801bed52840 0x03ef8090037daa50 0xffe0f803fffffc7f 0x9fffc1f007fffff8

def z487 : W := mkw 0x581da00353005030 0x12b03b4006a600a0 0x981f0003c3007c73 0xdb303e00078600f8

def z488 : W := mkw 0x5814a00000000000 0x02b0294000000000 0x981f000000000002 0x43303e0000000000

def z489 : W := mkw 0x083ef6fe210ae1a1 0x20107dedfc4215c3 0x001ffffc000063b0 0x60003ffff80000c7

def z490 : W := mkw 0x00094803ffd57870 0x1000129007ffaaf0 0x00000003fffffc40 0x1c00000007fffff8

def z491 : W := mkw 0x0000000080900000 0x0000000001012000 0x00000003c0f80040 0x1c0000000781f000

def z492 : W := mkw 0xf7c67f942c662eca 0x27ef8cff2858cc5d 0xe687ff1c3ce67ffd 0xb7cd0ffe3879ccff

def z493 : W := mkw 0xdd76a4c800000000 0x23baed4990000000 0xf97ff8e000000037 0xc3f2fff1c0000000

def z494 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xf9fff8fc00000006 0x43f3fff1f8000000

def z495 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6080f81c3ce67fc4 0x14c101f03879ccff

def z496 : W := mkw 0x000b05a24028570c 0x0800160b448050ae 0x011f07e200187ffa 0xec023e0fc40030ff

def z497 : W := mkw 0xf7c0000192910000 0x03ef800003252200 0xffe00003c319800f 0x8bffc00007863300

def z498 : W := mkw 0x000b5fb6642a7fce 0x0c0016bf6cc854ff 0x001ffffc00007fb0 0x60003ffff80000ff

def z499 : W := mkw 0xa7e217dc0866068a 0x254fc42fb810cc0d 0x07e007fc00e60388 0x240fc00ff801cc07

def z500 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x0680071c3ce67fc8 0x340d000e3879ccff

def z501 : W := mkw 0x0009480377007870 0x1000129006ee00f0 0x801f0003ff007c73 0xdb003e0007fe00f8

def z502 : W := mkw 0x0839c16ee1baf7ad 0x08107382ddc375ef 0x19f8c0ffe3ffffde 0xfc33f181ffc7ffff

def z503 : W := mkw 0x0000480024002840 0x0000009000480050 0x000000003c007c40 0x10000000007800f8

def z504 : W := mkw 0xf7c04905bef72eca 0x07ef80920b7dee5d 0xffe00003ffffffcf 0x9fffc00007ffffff

def z505 : W := mkw 0x0009480265007870 0x1000129004ca00f0 0x0000000000007c00 0x00000000000000f8

def z506 : W := mkw 0x0830c04c2102a0a1 0x0010618098420541 0x18e0c01c2307e3dc 0xa431c18038460fc7

def z507 : W := mkw 0x0008002200084100 0x0000100044001082 0x001800e000006390 0x60003001c00000c7

def z508 : W := mkw 0x00090122c0b8570c 0x08001202458170ae 0x011800e3c0f87fda 0xfc023001c781f0ff

def z509 : W := mkw 0x0830804800000000 0x0010610090000000 0x0018c0fc00000010 0x60003181f8000000

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080c01c0000001c 0xa001018038000000

def z511 : W := mkw 0x5000480136002840 0x02a00090026c0050 0xf800f803ff007c77 0x9bf001f007fe00f8

def z512 : W := mkw 0x22895b166c667eca 0x044512b62cd8ccfd 0xe69fff1ffce67fff 0xffcd3ffe3ff9ccff

def z513 : W := mkw 0x8d3b84eac198d125 0x091a7709d58331a2 0x997f00e3c3198002 0x4b32fe01c7863300

def z514 : W := mkw 0x081de80265007870 0x10103bd004ca00f0 0x181ff80223007c76 0xc8303ff0044600f8

def z515 : W := mkw 0xa780000088d40000 0x014f00000111a800 0xe7800003fcfe004f 0x9fcf000007f9fc00

def z516 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xff7f3fe000000023 0x43fefe7fc0000000

def z517 : W := mkw 0x500d680377007870 0x12a01ad006ee00f0 0xe0073803ff007c61 0x1bc00e7007fe00f8

def z518 : W := mkw 0x000009000c640e4a 0x040000120018c81c 0x000000001ce01c00 0x100000000039c038

def z519 : W := mkw 0x2280400428462080 0x0045008008508c41 0x6680c01c3ce663dd 0xb4cd01803879ccc7

def z520 : W := mkw 0x8d3bc5eee1baf7ad 0x091a778bddc375ef 0x871fc7ffc0f87ffb 0xff0e3f8fff81f0ff

def z521 : W := mkw 0x2ab8d37e296ee7ab 0x045571a6fc52ddcf 0x1ff8c7fe23ffe3de 0xec3ff18ffc47ffc7

def z522 : W := mkw 0x581de90377207e78 0x12b03bd206ee40fc 0xfe1fff03ffe07fff 0xfffc3ffe07ffc0ff

def z523 : W := mkw 0xa7831f90ccf41e4e 0x0d4f063f2199e83c 0xe6073f01dce01c21 0x13cc0e7e03b9c038

def z524 : W := mkw 0x0838806a0108c121 0x00107100d4021182 0x197800e20319e3da 0xec32f001c40633c7

def z525 : W := mkw 0x00084026210ae1a1 0x000010804c4215c3 0x0080c01e231fe3dc 0xac0101803c463fc7

def z526 : W := mkw 0xdd7fa4eac0985104 0x2bbaff49d58130a2 0x997f00e3c0180002 0x4b32fe01c7803000

def z527 : W := mkw 0xffffb7fbdafd570c 0x2bffff6ff7b5faae 0xffffffffffffffff 0xffffffffffffffff

def z528 : W := mkw 0xff9fffb7fffe7ffe 0x1fff3fff6ffffcff 0xff9ffffffffe7fff 0xffff3ffffffffcff

def z529 : W := mkw 0x0838806a0108c121 0x00107100d4021182 0x19f800e2231f804e 0xcc33f001c4463f00

def z530 : W := mkw 0x000849262d6eefeb 0x040010924c5adddf 0x000000023fffffc0 0x1c000000047fffff

def z531 : W := mkw 0x0000000000000000 0x0000000000000000 0x1960000203198002 0x0832c00004063300

def z532 : W := mkw 0xfffef6ffbbdfe1a1 0x23fffdedff77bfc3 0xffffffffffffe3ff 0xffffffffffffffc7

def z533 : W := mkw 0xd540000192910000 0x03aa800003252200 0xf9600003ff198047 0x9bf2c00007fe3300

def z534 : W := mkw 0x8d3fb7fac0b8570c 0x291a7f6ff58170ae 0x871fffffc0f87ffb 0xff0e3fffff81f0ff

def z535 : W := mkw 0xdd1fed83f7b07e7c 0x1bba3fdb07ef60fc 0xfe1fff03ffe07c77 0xdbfc3ffe07ffc0f8

def z536 : W := mkw 0x5040000112010000 0x02a0800002240200 0x1860000003018000 0x0030c00000060300

def z537 : W := mkw 0x5814a00000000000 0x02b0294000000000 0x7800f80000000004 0x00f001f000000000

def z538 : W := mkw 0x083bc5ee612af7ad 0x0810778bdcc255ef 0x19ffc7fe231ffffe 0xec33ff8ffc463fff

def z539 : W := mkw 0x00005b1424222eca 0x040000b62848445d 0x0600ff1c00e07ff9 0xb40c01fe3801c0ff

def z540 : W := mkw 0xfffffffeecfe7fce 0x2ffffffffdd9fcff 0xfffffffffcfe7fff 0xfffffffffff9fcff

def z541 : W := mkw 0xd54b05a3d2b9570c 0x0baa960b47a572ae 0x9f7f07e3c3f9fffb 0xff3efe0fc787f3ff

def z542 : W := mkw 0x8502048000000000 0x010a040900000000 0x070007e000000008 0x200e000fc0000000

def z543 : W := mkw 0xf7c05b142c662eca 0x07ef80b62858cc5d 0xffe0ff1c3ce67fff 0xb7ffc1fe3879ccff

def z544 : W := mkw 0x0020006c000a8181 0x00004000d8001503 0x000000fc00000380 0x20000001f8000007

def z545 : W := mkw 0x581ce00221006020 0x02b039c0044200c0 0xf81ff80223006077 0xcbf03ff0044600c0

def z546 : W := mkw 0x00090022c0985104 0x08001200458130a2 0x00000003c0180000 0x0800000007803000

def z547 : W := mkw 0x581de827770af9f1 0x12b03bd04eee15f3 0xf81ff803ff1ffff7 0xdff03ff007fe3fff

def z548 : W := mkw 0x0819c00261007020 0x0010338004c200e0 0x981fc003e3007c77 0xdb303f8007c600f8

def z549 : W := mkw 0x000949077f667efa 0x140012920efeccfd 0x00000003ffe67fc0 0x1c00000007ffccff

def z550 : W := mkw 0x2ab8da7e2d4ee9e3 0x045571b4fc5a9dd3 0x79f8f8fe3f1fe3de 0xecf3f1f1fc7e3fc7

def z551 : W := mkw 0x00090122c0b8570c 0x08001202458170ae 0x801f0003c0f87ff3 0xdf003e000781f0ff

def z552 : W := mkw 0x5814e80137002870 0x12b029d0026e0050 0xf800f803ff000047 0x9bf001f007fe0000

def z553 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x811f07e3c0187fb2 0x6b023e0fc78030ff

def z554 : W := mkw 0x0009010240205608 0x00001202048040ac 0x861f0703c0e07ffb 0xff0c3e0e0781c0ff

def z555 : W := mkw 0x850b04a2c0985104 0x090a1609458130a2 0x871f07e3c018003b 0xeb0e3e0fc7803000

def z556 : W := mkw 0x0020004800000000 0x0000400090000000 0x01e000fc00000008 0x2003c001f8000000

def z557 : W := mkw 0xd50f2da3d6b85f5c 0x1baa1e5b47ad70be 0xe71f3fe3dcf87ffb 0xffce3e7fc7b9f0ff

def z558 : W := mkw 0x2ab8c06e294ee1a1 0x00557180dc529dc3 0x7ff8c0fe3fffe3df 0xfcfff181fc7fffc7

def z559 : W := mkw 0x0000480137002870 0x10000090026e0050 0x000000003f000000 0x00000000007e0000

def z560 : W := mkw 0xfffffffbf7b87f7c 0x3bfffffff7ef70fe 0xfffffffffff87fff 0xfffffffffffff0ff

def z561 : W := mkw 0xa7805b14acf62eca 0x054f00b62959ec5d 0xe780ff1ffcfe7fff 0xbfcf01fe3ff9fcff

def z562 : W := mkw 0x7af4b25800000000 0x22f5e964b0000000 0x7ee0ff1c0000003d 0xa0fdc1fe38000000

def z563 : W := mkw 0x0028406e210ae1a1 0x00005080dc4215c3 0x01e000fe231fe3c8 0x2c03c001fc463fc7

def z564 : W := mkw 0x22801b100c640e4a 0x044500362018c81c 0x66803f003ce61c6d 0x94cd007e0079cc38

def z565 : W := mkw 0x0000000400020080 0x0000000008000401 0x0080001c00060388 0x2401000038000c07

def z566 : W := mkw 0xfff7bed956001850 0x33ffef7db2ac0030 0xfffffffddc001c3f 0xf3fffffffbb80038

def z567 : W := mkw 0x72c000011a450000 0x02e5800002348a00 0x600000001c000000 0x00c0000000380000

def z568 : W := mkw 0x72c05b153e672eca 0x06e580b62a7cce5d 0x7ee0ff1c3fe7fffd 0xb4fdc1fe387fcfff

def z569 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x86070703c0f87fe1 0x1f0c0e0e0781f0ff

def z570 : W := mkw 0x7a9dfa177f4678f2 0x16f53bf42efe8cf1 0xf89ff81fff067c77 0xdbf13ff03ffe0cf8

def z571 : W := mkw 0x000b04a240085104 0x08001609448010a2 0x001f00e000000000 0x40003e01c0000000

def z572 : W := mkw 0x8d3ac5eea1bae7ad 0x091a758bdd4375cf 0x1ff8c7fe23ffe3de 0xec3ff18ffc47ffc7

def z573 : W := mkw 0x8d36b6d800000000 0x211a6d6db0000000 0x871ffffc0000003b 0xe30e3ffff8000000

def z574 : W := mkw 0x0818c00221006020 0x00103180044200c0 0x19f8c002231fe05e 0xcc33f18004463fc0

def z575 : W := mkw 0x85030580c0b0160c 0x090a060b0181602c 0x87070703c0f81c6b 0x9f0e0e0e0781f038

def z576 : W := mkw 0x5814a00113000030 0x12b0294002260000 0x1800000003000000 0x0030000000060000

def z577 : W := mkw 0xfff6a4c99ad50000 0x23ffed499335aa00 0xffff00e3ffff804f 0xdffffe01c7ffff00

def z578 : W := mkw 0xffffb6da40005000 0x23ffff6db48000a0 0xffffffffc0007c7f 0xfbffffffff8000f8

def z579 : W := mkw 0xfff6ffdc24222eca 0x27ffedffb848445d 0xfffffffc00007fbf 0xe3fffffff80000ff

def z580 : W := mkw 0x72c000011a450000 0x02e5800002348a00 0x79e000023f1f804e 0x8cf3c000047e3f00

def z581 : W := mkw 0xf7c205a19afd070c 0x0bef840b4335fa0e 0xffe007e3ffff83cf 0xbfffc00fc7ffff07

def z582 : W := mkw 0x2280000008440000 0x0045000000108800 0x608000003c060004 0x00c1000000780c00

def z583 : W := mkw 0xf7c05a15bed728c2 0x07ef80b42b7dae51 0xffe0f81fffff804f 0x9fffc1f03fffff00

def z584 : W := mkw 0xf7c0000112000000 0x03ef800002240000 0xffe00003ff00004f 0x9bffc00007fe0000

def z585 : W := mkw 0x850b5fb6e4ba7fce 0x0d0a16bf6dc974ff 0x871fffffc0f87ffb 0xff0e3fffff81f0ff

def z586 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x0098c0fc200663dc 0xe4013181f8400cc7

def z587 : W := mkw 0xa7e216d800000000 0x214fc42db0000000 0x87ff07fc0000003b 0xe30ffe0ff8000000

def z588 : W := mkw 0x8500000080900000 0x010a000001012000 0x0700000000f80008 0x040e00000001f000

def z589 : W := mkw 0x0000400420022080 0x0000008008400441 0x0000c01c00006390 0x20000180380000c7

def z590 : W := mkw 0x5004200000000000 0x02a0084000000000 0xe007380000000021 0x03c00e7000000000

def z591 : W := mkw 0x0830804800000000 0x0010610090000000 0x197800e000000002 0x4032f001c0000000

def z592 : W := mkw 0xf7cb05a3dafd570c 0x0bef960b47b5faae 0xe71f07e3dcf87ffb 0xffce3e0fc7b9f0ff

def z593 : W := mkw 0x0000000000000000 0x0000000000000000 0x011800e00000001a 0xe0023001c0000000

def z594 : W := mkw 0xa78b17b2c0b8570c 0x094f162f658170ae 0xe79fffffc0f87fff 0xffcf3fffff81f0ff

def z595 : W := mkw 0xfff6b6d888d50000 0x23ffed6db111aa00 0xfffffffc00ff803f 0xe7fffffff801ff00

def z596 : W := mkw 0xa7eb17fac0b8570c 0x294fd62ff58170ae 0x87ff07ffc0f87ffb 0xff0ffe0fff81f0ff

def z597 : W := mkw 0xfff4b2599ad50000 0x23ffe964b335aa00 0xffe0f81fffff804f 0x9fffc1f03fffff00

def z598 : W := mkw 0xdd7ee4ee210ae1a1 0x23bafdc9dc4215c3 0x99ffc0fe231fe3de 0xef33ff81fc463fc7

def z599 : W := mkw 0x2ab0db5c2c662eca 0x045561b6b858cc5d 0x7ff8fffc3ce67fff 0xf4fff1fff879ccff

def z600 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x197800e2231fe3c2 0x4c32f001c4463fc7

def z601 : W := mkw 0x7adde8037f457870 0x12f5bbd006fe8af0 0xf8fff803ff07fc77 0xdbf1fff007fe0ff8

def z602 : W := mkw 0x00084026210ae1a1 0x000010804c4215c3 0x011800e2231fe3da 0xec023001c4463fc7

def z603 : W := mkw 0x0810c00021002020 0x0010218000420040 0x1800c00023000004 0x0030018000460000

def z604 : W := mkw 0x083bc5ee612af7ad 0x0810778bdcc255ef 0x001fc7fc00007fb0 0x60003f8ff80000ff

def z605 : W := mkw 0xf7c001019af50608 0x03ef80020335ea0c 0xffe00703ffffffff 0xbfffc00e07ffffff

def z606 : W := mkw 0xdd7feccb77007870 0x33baffd996ee00f0 0xf97ff8e3ff007c77 0xdbf2fff1c7fe00f8

def z607 : W := mkw 0x0000012080b8070c 0x080000024101700e 0x0000000000f80380 0x040000000001f007

def z608 : W := mkw 0x22895b177f667efa 0x144512b62efeccfd 0x6680ff1fffe67ffd 0xbccd01fe3fffccff

def z609 : W := mkw 0x0008002200084100 0x0000100044001082 0x011800e200180002 0x48023001c4003000

def z610 : W := mkw 0x0838db7e252aefeb 0x041071b6fc4a55df 0x19f8fffe231ffffe 0xec33f1fffc463fff

def z611 : W := mkw 0xdd7fa4cb53005030 0x33baff4996a600a0 0x997f00e3c3000002 0x4b32fe01c7860000

def z612 : W := mkw 0x0020006800088101 0x00004000d0001102 0x016000e000198000 0x0002c001c0003300

def z613 : W := mkw 0xffddfb17fff77efa 0x17ffbbf62fffeefd 0xffffff1fffffffff 0xfffffffe3fffffff

def z614 : W := mkw 0x0000010000200608 0x000000020000400c 0x0600070000e00388 0x240c000e0001c007

def z615 : W := mkw 0x7af0c04d3b47a0a1 0x02f5e1809a768f41 0x78e0c01c3f078004 0x00f1c180387e0f00

def z616 : W := mkw 0xffffffdf7f667efa 0x37ffffffbefeccfd 0xffffffffffe67fff 0xffffffffffffccff

def z617 : W := mkw 0x0000490024202e48 0x000000920048405c 0x6600ff003ce07ffd 0xb4cc01fe0079c0ff

def z618 : W := mkw 0x581feda377287f7c 0x1ab03fdb46ee50fe 0xf81fffe3ff007ff7 0xfbf03fffc7fe00ff

def z619 : W := mkw 0x00005b142c662eca 0x040000b62858cc5d 0x0000ff1c3ce67ff0 0x340001fe3879ccff

def z620 : W := mkw 0x000000019ad50000 0x000000000335aa00 0x00000001dce00000 0x1000000003b9c000

def z621 : W := mkw 0xffdffe9377007870 0x33ffbffd26ee00f0 0xfe1fff03ff007c77 0xdbfc3ffe07fe00f8

def z622 : W := mkw 0x72c05a153e4728c2 0x06e580b42a7c8e51 0x78e0f81c3f078004 0x00f1c1f0387e0f00

def z623 : W := mkw 0x0000000192910000 0x0000000003252200 0x00000003c3198000 0x0800000007863300

def z624 : W := mkw 0x00000024000a8181 0x0000000048001503 0x00000000001f8380 0x0400000000003f07

def z625 : W := mkw 0xdd76a4c800000000 0x23baed4990000000 0x9f7f07e00000003b 0xe33efe0fc0000000

def z626 : W := mkw 0xdd16a48000000000 0x03ba2d4900000000 0xff1fffe00000003f 0xe3fe3fffc0000000

def z627 : W := mkw 0x850b4da2e4b87f4c 0x090a169b45c970fe 0xe71fffe3fcf87fff 0xffce3fffc7f9f0ff

def z628 : W := mkw 0xf7c90003dad55000 0x03ef920007b5aaa0 0xffff0003fffffc7f 0xdffffe0007fffff8

def z629 : W := mkw 0x72805b153e662eca 0x06e500b62a7ccc5d 0xfe80ff1fffe67fff 0xbffd01fe3fffccff

def z630 : W := mkw 0x8d3b85eac1b8d72d 0x091a770bd58371ae 0x9f7f07e3c3f9fffb 0xff3efe0fc787f3ff

def z631 : W := mkw 0x2a98db162d666eea 0x045531b62c5accdd 0x7e98ff1e3fe67fff 0xfcfd31fe3c7fccff

def z632 : W := mkw 0xfff6b7d800200608 0x23ffed6fb000400c 0xfffffffc00e07fff 0xf7fffffff801c0ff

def z633 : W := mkw 0xfff6a4c800000000 0x23ffed4990000000 0xffff00e00000000f 0xc3fffe01c0000000

def z634 : W := mkw 0x0000010000200608 0x000000020000400c 0x0600070000e01c21 0x100c000e0001c038

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600070000000039 0xa00c000e00000000

def z636 : W := mkw 0xdd7fa5eac0b8570c 0x2bbaff4bd58170ae 0x9f7f07e3c0f87ffb 0xff3efe0fc781f0ff

def z637 : W := mkw 0xdd1fa5a2c0b8570c 0x0bba3f4b458170ae 0xff1fffe3c0f87fff 0xfffe3fffc781f0ff

def z638 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x01f8c0fc001fe398 0x6403f181f8003fc7

def z639 : W := mkw 0xf7c52801ded51850 0x13ef8a5003bdaa30 0xe6073801dce01c21 0x13cc0e7003b9c038

def z640 : W := mkw 0xfffbc5effbfff7ad 0x0bfff78bdff7ffef 0xffffc7ffffffffff 0xffffff8fffffffff

def z641 : W := mkw 0xffdfeda3fffd7f7c 0x1bffbfdb47fffafe 0xffffffe3ffffffff 0xffffffffc7ffffff

def z642 : W := mkw 0xf7c0000000000000 0x03ef800000000000 0xffe00002231f804f 0x8fffc00004463f00

def z643 : W := mkw 0x2ab8db7e2d6eefeb 0x045571b6fc5adddf 0x6698fffc3ce67ffd 0xf4cd31fff879ccff

def z644 : W := mkw 0xd540000000000000 0x03aa800000000000 0x9960000000000002 0x0332c00000000000

def z645 : W := mkw 0x72c000011a450000 0x02e5800002348a00 0xf8e00003ff078047 0x9bf1c00007fe0f00

def z646 : W := mkw 0x8d38c06ea19ae1a1 0x011a7180dd4335c3 0x9ff8c0ffe3ffe3df 0xff3ff181ffc7ffc7

def z647 : W := mkw 0xdd1de803f7907870 0x13ba3bd007ef20f0 0xff1ff803fff87c7f 0xdffe3ff007fff0f8

def z648 : W := mkw 0xd50b05a3d2b8570c 0x0baa160b47a570ae 0xff1f07e3fff87fff 0xfffe3e0fc7fff0ff

def z649 : W := mkw 0xa7e25fdc2c662eca 0x254fc4bfb858cc5d 0x67e0fffc3ce67ffd 0xb4cfc1fff879ccff

def z650 : W := mkw 0x5009000352005000 0x02a0120006a400a0 0xf81f0003ff007c77 0xdbf03e0007fe00f8

def z651 : W := mkw 0x000013140022068a 0x040000262800440d 0x0000071c00000380 0x2000000e38000007

def z652 : W := mkw 0x5814e80137002870 0x12b029d0026e0050 0x7800f8003f007c75 0x90f001f0007e00f8

def z653 : W := mkw 0x2a9dfb166d667efa 0x14553bf62cdaccfd 0x669fff1c3ce67ffd 0xf4cd3ffe3879ccff

def z654 : W := mkw 0xfff4b25800000000 0x23ffe964b0000000 0xffe0f81c0000000f 0x83ffc1f038000000

def z655 : W := mkw 0xfff6b7f880b8070c 0x2bffed6ff101700e 0xfffffffc00f803bf 0xe7fffffff801f007

def z656 : W := mkw 0x0830806c000a8181 0x00106100d8001503 0x19f8c0fc001f839e 0xe433f181f8003f07

def z657 : W := mkw 0x22801a100c440842 0x0445003420188810 0x600038001c000000 0x00c0007000380000

def z658 : W := mkw 0x8500000080900000 0x010a000001012000 0x86000001c0e00001 0x130c00000381c000

def z659 : W := mkw 0x850205a080b8070c 0x090a040b4101700e 0x870007e3c0f803cb 0xbf0e000fc781f007

def z660 : W := mkw 0xf7c94803ffd57870 0x13ef929007ffaaf0 0xffe00003fffffc4f 0x9fffc00007fffff8

def z661 : W := mkw 0x0000002000080100 0x0000000040001002 0x010000e000180388 0x24020001c0003007

def z662 : W := mkw 0x00005b1424222eca 0x040000b62848445d 0x6000ff1c3c007ff5 0xb0c001fe387800ff

def z663 : W := mkw 0x850205a080b8070c 0x090a040b4101700e 0x871f07e000f803bb 0xe70e3e0fc001f007

def z664 : W := mkw 0x8d3ac4ee210ae1a1 0x011a7589dc4215c3 0x9fffc7fe231fe3ff 0xef3fff8ffc463fc7

def z665 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf81ff803ff000006 0x4bf03ff007fe0000

def z666 : W := mkw 0xa7e216fc000a8181 0x214fc42df8001503 0x07e007fc001f8388 0x240fc00ff8003f07

def z667 : W := mkw 0x8500000000000000 0x010a000000000000 0x870000000000000b 0x830e000000000000

def z668 : W := mkw 0x8500000080900000 0x010a000001012000 0x9fe00003e3ff804f 0x9f3fc00007c7ff00

def z669 : W := mkw 0x00005b1424222eca 0x040000b62848445d 0x0080ff1c20067ffc 0xa40101fe38400cff

def z670 : W := mkw 0x581de923f7b87f7c 0x1ab03bd247ef70fe 0xf81ff803fff87ff7 0xdff03ff007fff0ff

def z671 : W := mkw 0x7af4fa5937002870 0x32f5e9f4b26e0050 0x78e0f81c3f000004 0x00f1c1f0387e0000

def z672 : W := mkw 0xfff0c04dbbd7a0a1 0x03ffe1809b77af41 0xffe0c01fffff804f 0x9fffc1803fffff00

def z673 : W := mkw 0xa7c0000088d50000 0x014f80000111aa00 0x67e000003cff804d 0x94cfc0000079ff00

def z674 : W := mkw 0x22a05b7c2c6eafcb 0x044540b6f858dd5f 0x67e0fffc3cfffffd 0xb4cfc1fff879ffff

def z675 : W := mkw 0x0020004c00028081 0x0000400098000501 0x00e0001c00078000 0x0001c00038000f00

def z676 : W := mkw 0x0838db7e252aefeb 0x041071b6fc4a55df 0x0018fffc00007fb0 0x600031fff80000ff

def z677 : W := mkw 0x581da00353005030 0x12b03b4006a600a0 0xf81f0003ff000047 0xdbf03e0007fe0000

def z678 : W := mkw 0x228013140866068a 0x044500262810cc0d 0x6680ff1c00e603bd 0xa4cd01fe3801cc07

def z679 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xfe000003ffe00047 0x9bfc000007ffc000

def z680 : W := mkw 0x00010100c0b0160c 0x080002020181602c 0x00000001c0e01c00 0x100000000381c038

def z681 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x0118c0fe001863da 0xec023181fc0030c7

def z682 : W := mkw 0xf7c6369000000000 0x23ef8c6d20000000 0xe687ff1c0000003d 0xa3cd0ffe38000000

def z683 : W := mkw 0x850204a080980104 0x090a040941013002 0x010000e000180000 0x00020001c0003000

def z684 : W := mkw 0x081dfb1665227efa 0x14103bf62cca44fd 0x001fff1c00007fb0 0x60003ffe380000ff

def z685 : W := mkw 0x00005a14240228c2 0x040000b428480451 0x0000f81c00000000 0x000001f038000000

def z686 : W := mkw 0x0818800201004020 0x0010310004020080 0x1818000203000002 0x4830300004060000

def z687 : W := mkw 0x00094126e1baf7ad 0x080012824dc375ef 0x00000003e3ffffc0 0x1c00000007c7ffff

def z688 : W := mkw 0xfff8806b9bddc121 0x03fff100d737bb82 0xfff800e3ffff804f 0xdffff001c7ffff00

def z689 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x0018c0fe231fe3d0 0x6c003181fc463fc7

def z690 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xe7000003dcf8004b 0x9fce000007b9f000

def z691 : W := mkw 0x0000000112000000 0x0000000002240000 0x00000003ff000040 0x1800000007fe0000

def z692 : W := mkw 0xf7c90123dafd570c 0x0bef920247b5faae 0xffe00003ffffffcf 0x9fffc00007ffffff

def z693 : W := mkw 0x7afcf27e210ae1a1 0x22f5f9e4fc4215c3 0x79f8f8fe231fe3de 0xecf3f1f1fc463fc7

def z694 : W := mkw 0x8d3284c800000000 0x011a650990000000 0x9fffc7fc0000003f 0xe33fff8ff8000000

def z695 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0x9fe00003c3ff800a 0x0f3fc0000787ff00

def z696 : W := mkw 0x0009000240005000 0x00001200048000a0 0x801f0003c0000002 0x4b003e0007800000

def z697 : W := mkw 0x0008002200084100 0x0000100044001082 0x19f800e2231fe3de 0xec33f001c4463fc7

def z698 : W := mkw 0x0838c96e2d6eefeb 0x04107192dc5adddf 0x19f8c0fe3fffffde 0xfc33f181fc7fffff

def z699 : W := mkw 0x5000000000000000 0x02a0000000000000 0xf800000000000007 0x83f0000000000000

def z700 : W := mkw 0x22885b362d6eefeb 0x044510b66c5adddf 0x6680ff1e3ffffffd 0xbccd01fe3c7fffff

def z701 : W := mkw 0xa7c205a088fd070c 0x094f840b4111fa0e 0x07e007e000ff8388 0x240fc00fc001ff07

def z702 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x19f8c0fc0000639e 0xe033f181f80000c7

def z703 : W := mkw 0x8d3b85eac0b8570c 0x091a770bd58170ae 0x9fffc7ffc0f87fff 0xff3fff8fff81f0ff

def z704 : W := mkw 0x5838c06f330ae1a1 0x02b07180de6615c3 0xf9f8c0ffff1fe3df 0xfff3f181fffe3fc7

def z705 : W := mkw 0x7a94fb142c662eca 0x06f529f62858cc5d 0xfe9fff1c3ce67fff 0xf7fd3ffe3879ccff

def z706 : W := mkw 0x0839c86f770af9f1 0x10107390deee15f3 0x19f8c0ffff1fffde 0xfc33f181fffe3fff

def z707 : W := mkw 0xdd76edcc2c662eca 0x27baeddb9858cc5d 0x997f00e03ce67fc2 0x5732fe01c079ccff

def z708 : W := mkw 0xdd16eda1b7b82f7c 0x1bba2ddb436f705e 0x7f00ffe03ff8038c 0x24fe01ffc07ff007

def z709 : W := mkw 0x581de82377087970 0x12b03bd046ee10f2 0xf81ff803ff187ff7 0xdff03ff007fe30ff

def z710 : W := mkw 0xf7c31f91def51e4e 0x0fef863f23bdea3c 0xe6073f01dce01c21 0x13cc0e7e03b9c038

def z711 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0xe69fff1c3ce67fff 0xf7cd3ffe3879ccff

def z712 : W := mkw 0x5814e80136002840 0x02b029d0026c0050 0xf81ff803ff007c77 0xdbf03ff007fe00f8

def z713 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xff600003ffff8043 0x1ffec00007ffff00

def z714 : W := mkw 0x500d680376007850 0x12a01ad006ec00f0 0xe01ff803fc007c77 0xdbc03ff007f800f8

def z715 : W := mkw 0xf7c420019ad50000 0x03ef88400335aa00 0xffe73803ffff806f 0x9fffce7007ffff00

def z716 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffc2307803f 0xe3fffffff8460f00

def z717 : W := mkw 0x083ce06e210ae1a1 0x001079c0dc4215c3 0x19fff8fe231fe3fe 0xec33fff1fc463fc7

def z718 : W := mkw 0x581de807770278f0 0x12b03bd00eee04f1 0xf81ff803ff067ff7 0xdff03ff007fe0cff

def z719 : W := mkw 0x8d33c5cce1b2b6ad 0x091a678b99c3656d 0x9ee7c71de3e79c25 0x133dcf8e3bc7cf38

def z720 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xe01ff803ff007c71 0x5bc03ff007fe00f8

def z721 : W := mkw 0x5009480376007840 0x02a0129006ec00f0 0xf81ff803ff007c77 0xdbf03ff007fe00f8

def z722 : W := mkw 0x7af4fa5d3e4728c2 0x26f5e9f4ba7c8e51 0x78e0f81c3f078004 0x00f1c1f0387e0f00

def z723 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xffe00003ffff8007 0x1bffc00007ffff00

def z724 : W := mkw 0xaff6b6d800000000 0x215fed6db0000000 0x061ffffc00000030 0x600c3ffff8000000

def z725 : W := mkw 0x581da80357005870 0x12b03b5006ae00b0 0xf81ff803df001c37 0xdbf03ff007be0038

def z726 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xe0073801fc001c65 0x93c00e7003f80038

def z727 : W := mkw 0xdd7fa4ebd3985134 0x3bbaff49d7a730a2 0x997f00e3c3180002 0x4b32fe01c7863000

def z728 : W := mkw 0xafb296d800000000 0x015f652db0000000 0xfffffffc0000003f 0xe3fffffff8000000

def z729 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xe69ffffc0000003d 0xe3cd3ffff8000000

def z730 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6600ff1c3ce07ff5 0xb0cc01fe3879c0ff

def z731 : W := mkw 0x5025286d560a99d1 0x12a04a50daac1533 0xe1e738fddc1f9fa9 0x37c3ce71fbb83f3f

def z732 : W := mkw 0x22c05b142c672eca 0x044580b62858ce5d 0x66e0ff1c3ce7fffd 0xb4cdc1fe3879cfff

def z733 : W := mkw 0x0830806c000a8181 0x00106100d8001503 0x19f8c0fe231f83de 0xec33f181fc463f07

def z734 : W := mkw 0x850b05a2c1b8d72d 0x090a160b458371ae 0x871f07e3c3f9fffb 0xff0e3e0fc787f3ff

def z735 : W := mkw 0xd5405b15b6b32eca 0x07aa80b62b6d665d 0x9960ff1fc319ffb2 0x2b32c1fe3f8633ff

def z736 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xf81ff8ffff1ffff7 0xfff03ff1fffe3fff

def z737 : W := mkw 0x00094926e4ba7fce 0x0c0012924dc974ff 0x00000003c0f87fc0 0x1c0000000781f0ff

def z738 : W := mkw 0x581de80264007840 0x02b03bd004c800f0 0xf81ff803fc007c77 0xdbf03ff007f800f8

def z739 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xfffffffdfce6007f 0xf7fffffffbf9cc00

def z740 : W := mkw 0x22801b100c640e4a 0x044500362018c81c 0x6680ff1c1ce07ffd 0xb4cd01fe3839c0ff

def z741 : W := mkw 0xf7c432119ad50000 0x23ef88642335aa00 0xffe03803ffff804f 0x9fffc07007ffff00

def z742 : W := mkw 0xf7ce76b6210ae1a1 0x23ef9ced6c4215c3 0xe6073f02231fe3e1 0x0fcc0e7e04463fc7

def z743 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xe007f801dc001c35 0x93c00ff003b80038

def z744 : W := mkw 0x581de82377087970 0x12b03bd046ee10f2 0xf91ff8e3ff187c77 0xdbf23ff1c7fe30f8

def z745 : W := mkw 0xf7c6369000000000 0x23ef8c6d20000000 0xe79ffffc0000003f 0xe3cf3ffff8000000

def z746 : W := mkw 0xfff6b6d913000030 0x33ffed6db2260000 0xfffffffc0300003f 0xe3fffffff8060000

def z747 : W := mkw 0x583de84f7702f8f1 0x12b07bd09eee05f1 0xf8fff81fff07ffff 0xfff1fff03ffe0fff

def z748 : W := mkw 0x2ab89b7a0d6ccf6b 0x04557136f41ad99e 0x7f783fe21ff99c23 0x58fef07fc43ff338

def z749 : W := mkw 0x500d680377007870 0x12a01ad006ee00f0 0xe01f3803ff007c73 0xdbc03e7007fe00f8

def z750 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xffe0f803ffff807f 0x9fffc1f007ffff00

def z751 : W := mkw 0xdd76b6d800000000 0x23baed6db0000000 0xf97ffffc00000037 0xe3f2fffff8000000

def z752 : W := mkw 0xd54000019ad50000 0x03aa80000335aa00 0xf9600003ffff8047 0x9ff2c00007ffff00

def z753 : W := mkw 0x0830c06c210aa1a1 0x00106180d8421543 0x19e0c0fe231f83ce 0xac33c181fc463f07

def z754 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf9fff803ff007c7f 0xdbf3fff007fe00f8

def z755 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x19f8c0fe231fffff 0xfc33f181fc463fff

def z756 : W := mkw 0x500d280356005850 0x12a01a5006ac00b0 0xf81f3803ff007c77 0xdbf03e7007fe00f8

def z757 : W := mkw 0xa7eb5edb77007870 0x314fd6bdb6ee00f0 0x07e007ffff007c48 0x380fc00ffffe00f8

def z758 : W := mkw 0x0836b6d99ad50000 0x20106d6db335aa00 0x001fffffffff8070 0x7c003fffffffff00

def z759 : W := mkw 0x583de84b77007870 0x12b07bd096ee00f0 0xf81ff8ffff007c77 0xfbf03ff1fffe00f8

def z760 : W := mkw 0xfff6b6d912000000 0x23ffed6db2240000 0xffffffffff1f807f 0xfffffffffffe3f00

def z761 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfe1ffffc00000037 0xe3fc3ffff8000000

def z762 : W := mkw 0x583de84b77007870 0x12b07bd096ee00f0 0xf9fff8ffff1ffc7f 0xfff3fff1fffe3ff8

def z763 : W := mkw 0x0000490424222ec8 0x000000920848445d 0x6680ff1c3ce67ffd 0xb4cd01fe3879ccff

def z764 : W := mkw 0x083fedee652afffd 0x18107fdbdcca55ff 0x001ffffc00007fb0 0x60003ffff80000ff

def z765 : W := mkw 0x5876b6d800000000 0x22b0ed6db0000000 0x187ffffc00000030 0x6030fffff8000000

def z766 : W := mkw 0x581da80357005870 0x12b03b5006ae00b0 0xe01f3801dc001c21 0x53c03e7003b80038

def z767 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x009ffffc0000003c 0xe0013ffff8000000

def z768 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xffffffffdcf8007f 0xffffffffffb9f000

def z769 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0x9ffffffc0000003a 0x633ffffff8000000

def z770 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xffffffffc3ff803f 0xefffffffff87ff00

def z771 : W := mkw 0x5815a80156001850 0x12b02b5002ac0030 0xf81f3801dc001c23 0x53f03e7003b80038

def z772 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x87ff07e3c0fffffb 0xff0ffe0fc781ffff

def z773 : W := mkw 0x583de86b7708f971 0x12b07bd0d6ee11f2 0xf9fff8ffff19fc7f 0xfbf3fff1fffe33f8

def z774 : W := mkw 0xf7c204819ad50000 0x03ef84090335aa00 0xffe007e3ffff804f 0xbfffc00fc7ffff00

def z775 : W := mkw 0x8d36b6d880900000 0x211a6d6db1012000 0x871fffffc0f8007b 0xff0e3fffff81f000

def z776 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf81ff803ff001c27 0x5bf03ff007fe0038

def z777 : W := mkw 0x7a9db3175b6656ba 0x16f53b662eb6ccad 0x9e9f071fc3e6038a 0x6f3d3e0e3f87cc07

def z778 : W := mkw 0x7afdb37ac0b8570c 0x2af5fb66f58170ae 0x78e0f81fc0f87fc4 0x1cf1c1f03f81f0ff

def z779 : W := mkw 0x0009012240285708 0x00001202448050ae 0x871f07e3c0f87ffb 0xff0e3e0fc781f0ff

def z780 : W := mkw 0x0839c06e610af1a1 0x00107380dcc215e3 0x19f8c0ffe31fffde 0xfc33f181ffc63fff

def z781 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xe0073803ff001c61 0x1bc00e7007fe0038

def z782 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xf9fffffc00000036 0x63f3fffff8000000

def z783 : W := mkw 0x583de84f7702f8f1 0x12b07bd09eee05f1 0xf9fff8ffff07fc7f 0xfbf3fff1fffe0ff8

def z784 : W := mkw 0x500d6827770af9f1 0x12a01ad04eee15f3 0xe0073803ff1fffe1 0x1fc00e7007fe3fff

def z785 : W := mkw 0x081de80265007870 0x10103bd004ca00f0 0xe01ff803fc007c77 0xdbc03ff007f800f8

def z786 : W := mkw 0x5815a80156001850 0x12b02b5002ac0030 0xf81ff803ff001c77 0xdbf03ff007fe0038

def z787 : W := mkw 0xd500000192900000 0x03aa000003252000 0xffe00003ffff804f 0x9fffc00007ffff00

def z788 : W := mkw 0x00094927f7bafffd 0x180012924fef75ff 0x00000003ffffffc0 0x1c00000007ffffff

def z789 : W := mkw 0x583de86b7708f971 0x12b07bd0d6ee11f2 0xf9fff8e3ff1ffc7f 0xdff3fff1c7fe3ff8

def z790 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xffffffffc000007f 0xfbffffffff800000

def z791 : W := mkw 0x585de80377017870 0x12b0bbd006ee02f0 0xf87ff803ff01fc77 0xdbf0fff007fe03f8

def z792 : W := mkw 0xf7c73791daf5160c 0x2bef8e6f23b5ea2c 0xe6073f01dce01c21 0x13cc0e7e03b9c038

def z793 : W := mkw 0x581de827770af9f1 0x12b03bd04eee15f3 0xf81ff803ff007ff7 0xdbf03ff007fe00ff

def z794 : W := mkw 0x5836b6d800000000 0x22b06d6db0000000 0xf9fffffc0000003f 0xe3f3fffff8000000

def z795 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xffe00003ffffe3df 0xbfffc00007ffffc7

def z796 : W := mkw 0xfff6b6d888d50000 0x23ffed6db111aa00 0xfffffffc00e0003f 0xe3fffffff801c000

def z797 : W := mkw 0x500000019ad50000 0x02a000000335aa00 0xf9e00003ffff804f 0x9ff3c00007ffff00

def z798 : W := mkw 0xf7c216919ad50000 0x23ef842d2335aa00 0xffe00703ffff804f 0x9fffc00e07ffff00

def z799 : W := mkw 0x728000011a440000 0x02e5000002348800 0xffe00003ffff804f 0x9fffc00007ffff00

def z800 : W := mkw 0xf7c204819ad50000 0x03ef84090335aa00 0xffe70703ffff806f 0x9fffce0e07ffff00

def z801 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6680ff1e3ffffffd 0xbccd01fe3c7fffff

def z802 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x19f8c0fe231fe3c6 0x4c33f181fc463fc7

def z803 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x9f7f07e3c3f9fffb 0xff3efe0fc787f3ff

def z804 : W := mkw 0xfff6b6d808440000 0x23ffed6db0108800 0xfffffffc1ce0003f 0xf3fffffff839c000

def z805 : W := mkw 0x72c000019ad50000 0x02e580000335aa00 0x7ee00003ffff804d 0x9cfdc00007ffff00

def z806 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x879fc7ffc0f87fff 0xff0f3f8fff81f0ff

def z807 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xf97ff8e3ff1ffff7 0xdff2fff1c7fe3fff

def z808 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffc0000000e 0x63fffffff8000000

def z809 : W := mkw 0x0020006c000a8181 0x00004000d8001503 0x19e000fc231f838c 0x2433c001f8463f07

def z810 : W := mkw 0xa7a217fc88fe878f 0x0d4f442ff911fd0f 0x07e007fc00ff8388 0x240fc00ff801ff07

def z811 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6780ff1e3cfe7fff 0xbccf01fe3c79fcff

def z812 : W := mkw 0xfff6b6d880900000 0x23ffed6db1012000 0xffffffffc018003f 0xebffffffff803000

def z813 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xf9e73803ff1f9c6f 0x9ff3ce7007fe3f38

def z814 : W := mkw 0x500d280356005850 0x12a01a5006ac00b0 0xe01f3803dc001c23 0x5bc03e7007b80038

def z815 : W := mkw 0x0028406e210ae1a1 0x00005080dc4215c3 0x19e000fe231fe3ce 0xac33c001fc463fc7

def z816 : W := mkw 0xf7c216919ad50000 0x03ef842d2335aa00 0xffffffffffff807f 0xffffffffffffff00

def z817 : W := mkw 0x5815e80177003870 0x12b02bd002ee0070 0xf807f801ff007c75 0x93f00ff003fe00f8

def z818 : W := mkw 0x0839c86e650af9f1 0x10107390dcca15f3 0x19f8c0fe231fffde 0xec33f181fc463fff

def z819 : W := mkw 0x0839c86e650af9e1 0x00107390dcca15f3 0xf9fff8ffff1fffff 0xfff3fff1fffe3fff

def z820 : W := mkw 0x8502058080b00608 0x010a040b0101600c 0x871f07e3c0f87ffb 0xff0e3e0fc781f0ff

def z821 : W := mkw 0xfff6b6d880900000 0x23ffed6db1012000 0xffffffffe3ff807f 0xffffffffffc7ff00

def z822 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf8fff803ff07fc77 0xdbf1fff007fe0ff8

def z823 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf81ff803ff1ffc77 0xdff03ff007fe3ff8

def z824 : W := mkw 0xaff6b6d888d50000 0x215fed6db111aa00 0x07fffffc00ff8038 0x640ffffff801ff00

def z825 : W := mkw 0x583de86b77087970 0x12b07bd0d6ee10f2 0xf9fff8ffff187fff 0xfff3fff1fffe30ff

def z826 : W := mkw 0x581de827770af9f1 0x12b03bd04eee15f3 0xf91ff8e3ff1fffff 0xfff23ff1c7fe3fff

def z827 : W := mkw 0xdd36a4c800000000 0x03ba6d4990000000 0xfffffffc0000003f 0xe3fffffff8000000

def z828 : W := mkw 0x0838806e010ac1a1 0x00107100dc021583 0x19f8c0fe031f839e 0xec33f181fc063f07

def z829 : W := mkw 0x583de84f770278f0 0x12b07bd09eee04f1 0xf9fff8ffff067fff 0xfff3fff1fffe0cff

def z830 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xe61ffffddce00031 0x73cc3ffffbb9c000

def z831 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0xe71fffe3c0f87fff 0xffce3fffc781f0ff

def z832 : W := mkw 0xa782169088d40000 0x014f042d2111a800 0xe79ffffffcfe007f 0xffcf3ffffff9fc00

def z833 : W := mkw 0xfff6b6d912000000 0x23ffed6db2240000 0xfffffffc3f00003f 0xe3fffffff87e0000

def z834 : W := mkw 0xf7c012119ad50000 0x03ef80242335aa00 0xffe03f03ffff806f 0x9fffc07e07ffff00

def z835 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0x7fe00003ffff804c 0x1cffc00007ffff00

def z836 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf89ff803ff067c7f 0xdff13ff007fe0cf8

def z837 : W := mkw 0xfff6b6d808440000 0x23ffed6db0108800 0xfffffffc3c06003f 0xe3fffffff8780c00

def z838 : W := mkw 0xf7c624819ad50000 0x23ef8c490335aa00 0xffe70003ffff804f 0x9fffce0007ffff00

def z839 : W := mkw 0x0838806a00084100 0x00107100d4001082 0x19f8c0fe231fe3de 0xec33f181fc463fc7

def z840 : W := mkw 0x000b05a24028570c 0x0800160b448050ae 0x861f07e3c0e07ffb 0xff0c3e0fc781c0ff

def z841 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xfffffffddcff803f 0xf7fffffffbb9ff00

def z842 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf81ff801dc007c37 0xd3f03ff003b800f8

def z843 : W := mkw 0xfff8c06fbbdfe1a1 0x03fff180df77bfc3 0xe618c0fddce06391 0x73cc3181fbb9c0c7

def z844 : W := mkw 0x504000019ad50000 0x02a080000335aa00 0x18600003ffff8040 0x1c30c00007ffff00

def z845 : W := mkw 0x581da80357005870 0x12b03b5006ae00b0 0xf81f3803ff001c67 0xdbf03e7007fe0038

def z846 : W := mkw 0x7af6b6d800000000 0x22f5ed6db0000000 0x601ffffc00000030 0x60c03ffff8000000

def z847 : W := mkw 0x0028006e000ac181 0x00005000dc001583 0x19f800fe231fe3de 0xec33f001fc463fc7

def z848 : W := mkw 0x000949266c6e7fce 0x0c0012924cd8dcff 0x000000003ce67fc0 0x140000000079ccff

def z849 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x19f8c0fc231fe39c 0x6433f181f8463fc7

def z850 : W := mkw 0x5836b6d800000000 0x22b06d6db0000000 0x981ffffc00000032 0x63303ffff8000000

def z851 : W := mkw 0x583de86b7708f971 0x12b07bd0d6ee11f2 0xf81ff8e3ff007c77 0xdbf03ff1c7fe00f8

def z852 : W := mkw 0x000000019ad50000 0x000000000335aa00 0x19600003ffff8042 0x1c32c00007ffff00

def z853 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x7e80ff1e3fe67fff 0xbcfd01fe3c7fccff

def z854 : W := mkw 0x5005680176003850 0x12a00ad002ec0070 0xf807f803ff007c77 0x9bf00ff007fe00f8

def z855 : W := mkw 0xf7c63f919ef50e4a 0x27ef8c7f233dea1c 0xe6073f01dce01c21 0x13cc0e7e03b9c038

def z856 : W := mkw 0x72cb05a35a6d570c 0x0ae5960b46b4daae 0x78ff07e03f07ffb4 0x60f1fe0fc07e0fff

def z857 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x061ffffc00000039 0xe00c3ffff8000000

def z858 : W := mkw 0xf7c636919ad50000 0x23ef8c6d2335aa00 0xffff3fe3ffff807f 0xfffffe7fc7ffff00

def z859 : W := mkw 0xf7c2169000000000 0x03ef842d20000000 0xfffffffc0000003f 0xe3fffffff8000000

def z860 : W := mkw 0xafdde802edd57870 0x115fbbd005dbaaf0 0x07fff80000fffc38 0x440ffff00001fff8

def z861 : W := mkw 0x5815a80156001850 0x12b02b5002ac0030 0xf807f801dc001c25 0x13f00ff003b80038

def z862 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6680ff1c1ce67fb9 0x34cd01fe3839ccff

def z863 : W := mkw 0x00094826640a79c0 0x000012904cc814f3 0xe19ff8fffc1e7fff 0xffc33ff1fff83cff

def z864 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffe0018007f 0xeffffffffc003000

def z865 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x99ffc0fe231fe3ff 0xef33ff81fc463fc7

def z866 : W := mkw 0xa7e217dc88f7068a 0x254fc42fb911ee0d 0x07e007fc00ff8388 0x240fc00ff801ff07

def z867 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf97ff803ff19fc77 0xdbf2fff007fe33f8

def z868 : W := mkw 0xfff6b6d880900000 0x23ffed6db1012000 0xfffffffdc0e0003f 0xf3fffffffb81c000

def z869 : W := mkw 0x0020006c000a8181 0x00004000d8001503 0x19e000fe031f838a 0x2c33c001fc063f07

def z870 : W := mkw 0x581de807770278f0 0x12b03bd00eee04f1 0xf89ff81fff067c77 0xdbf13ff03ffe0cf8

def z871 : W := mkw 0xfff6b6d808440000 0x23ffed6db0108800 0xfffffffe3fff807f 0xfffffffffc7fff00

def z872 : W := mkw 0x00094927fffe7ffe 0x1c0012924ffffcff 0x00000003fffe7fc0 0x1c00000007fffcff

def z873 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xffe00703ffff807f 0xbfffc00e07ffff00

def z874 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xffffffffdff9803f 0xfbffffffffbff300

def z875 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffc000063ff 0xe7fffffff80000c7

def z876 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x871f07e3c0f87fca 0x7f0e3e0fc781f0ff

def z877 : W := mkw 0xa78b5eb6ecde79c6 0x0d4f16bd6dd9bcf3 0xe19ff8fffc1e0006 0x4bc33ff1fff83c00

def z878 : W := mkw 0xf7c204819ad50000 0x03ef84090335aa00 0xffff00e3ffff804f 0xdffffe01c7ffff00

def z879 : W := mkw 0x5005680176003850 0x12a00ad002ec0070 0xe0073801fc007c61 0x13c00e7003f800f8

def z880 : W := mkw 0x083dfb7e652afffb 0x14107bf6fcca55ff 0x001ffffc00007fb0 0x60003ffff80000ff

def z881 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf91ff803ff187c7f 0xdff23ff007fe30f8

def z882 : W := mkw 0x8d76b6d800000000 0x211aed6db0000000 0x017ffffc00000030 0x6002fffff8000000

def z883 : W := mkw 0x72c000019ad50000 0x02e580000335aa00 0xf8e00003ffff8047 0x9ff1c00007ffff00

def z884 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xf8073801dc001c27 0x93f00e7003b80038

def z885 : W := mkw 0x000949277f6efffb 0x140012924efeddff 0x00000003ffffffc0 0x1c00000007ffffff

def z886 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0xe71f07e3fcf87fff 0xffce3e0fc7f9f0ff

def z887 : W := mkw 0x00094926642a7fce 0x0c0012924cc854ff 0x0000000000007f80 0x00000000000000ff

def z888 : W := mkw 0x500d680377007870 0x12a01ad006ee00f0 0xe0073801dc007c21 0x13c00e7003b800f8

def z889 : W := mkw 0x581de82377087970 0x12b03bd046ee10f2 0xf81ff8e3ff007ff7 0xfbf03ff1c7fe00ff

def z890 : W := mkw 0x72c000019ad50000 0x02e580000335aa00 0x79e00003ffff804e 0x9cf3c00007ffff00

def z891 : W := mkw 0xa7e216d800000000 0x214fc42db0000000 0xe7fffffc0000003f 0xe3cffffff8000000

def z892 : W := mkw 0x0020406c200aa181 0x00004080d8401543 0x19e0c0fe231fe3de 0xac33c181fc463fc7

def z893 : W := mkw 0x5815a80157001870 0x12b02b5002ae0030 0xf8073801df001c21 0x13f00e7003be0038

def z894 : W := mkw 0xfff6b6d91a450000 0x23ffed6db2348a00 0xffffffffff07807f 0xfbfffffffffe0f00

def z895 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6680ff1c3ce67fbc 0x24cd01fe3879ccff

def z896 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6798fffc3ce67fff 0xf4cf31fff879ccff

def z897 : W := mkw 0xf7c012119ad50000 0x03ef80242335aa00 0xffe0f81fffff804f 0x9fffc1f03fffff00

def z898 : W := mkw 0x5005680176003850 0x12a00ad002ec0070 0xe007f801dc007c31 0x13c00ff003b800f8

def z899 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x601ffffc00000035 0xe0c03ffff8000000

def z900 : W := mkw 0x0830806c010a81a1 0x00106100d8021503 0x19e000fc031f8388 0x2433c001f8063f07

def z901 : W := mkw 0x0819c80265007860 0x0010339004ca00f0 0xf81ff803ff007c77 0xdbf03ff007fe00f8

def z902 : W := mkw 0xa78217b088fc070e 0x0d4f042f6111f80e 0x070007e000f80388 0x240e000fc001f007

def z903 : W := mkw 0x50056805760238d0 0x12a00ad00aec0471 0xe087f81dfc067ffd 0xb7c10ff03bf80cff

def z904 : W := mkw 0x7ab4fa5d3f46a8f3 0x16f569f4ba7e8d51 0x78e0f81c3f078004 0x00f1c1f0387e0f00

def z905 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xffffffffffe0007f 0xfbffffffffffc000

def z906 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x01fffffc00000038 0x6003fffff8000000

def z907 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xffffffffff1f803f 0xebfffffffffe3f00

def z908 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x9fff07e3c0f87fff 0xff3ffe0fc781f0ff

def z909 : W := mkw 0xfff6b6d912010000 0x23ffed6db2240200 0xfffffffc0301803f 0xe3fffffff8060300

def z910 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xf8fff81fff1ffff7 0xdff1fff03ffe3fff

def z911 : W := mkw 0x581da80356005850 0x12b03b5006ac00b0 0xf81ff803dc007c77 0xdbf03ff007b800f8

def z912 : W := mkw 0xfff6b6d808450000 0x23ffed6db0108a00 0xfffffffc0007803f 0xe3fffffff8000f00

def z913 : W := mkw 0xfff6b6d992900000 0x23ffed6db3252000 0xfffffffffff8007f 0xfffffffffffff000

def z914 : W := mkw 0xdd76b6d800000000 0x23baed6db0000000 0x9f7ffffc0000003b 0xe33efffff8000000

def z915 : W := mkw 0xd54000019ad50000 0x03aa80000335aa00 0x9f600003ffff804b 0x9f3ec00007ffff00

def z916 : W := mkw 0x5815e80177003870 0x12b02bd002ee0070 0xf807f803ff001c67 0x9bf00ff007fe0038

def z917 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6680ff1c3ce67fe5 0x14cd01fe3879ccff

def z918 : W := mkw 0xfff6b6d888d40000 0x23ffed6db111a800 0xfffffffffcfe007f 0xfffffffffff9fc00

def z919 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xe01ff8fddc007fb1 0x73c03ff1fbb800ff

def z920 : W := mkw 0x854b05a2c0b9570c 0x090a960b458172ae 0x877f07e3c0f9fffb 0xff0efe0fc781f3ff

def z921 : W := mkw 0x0838c86e250ae9e1 0x00107190dc4a15d3 0x79f8f8fe3f1fe3de 0xecf3f1f1fc7e3fc7

def z922 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffc00e0007f 0xf7fffffff801c000

def z923 : W := mkw 0xfff6b6d912000000 0x23ffed6db2240000 0xfffffffddc00003f 0xf3fffffffbb80000

def z924 : W := mkw 0x581de827770af9f1 0x12b03bd04eee15f3 0xf89ff81fff1fffff 0xfff13ff03ffe3fff

def z925 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffc001f803f 0xe7fffffff8003f00

def z926 : W := mkw 0xdd3fa4ebd398d135 0x1bba7f49d7a731a2 0x997f00e3c3198002 0x4b32fe01c7863300

def z927 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xffe00003fffffc7f 0x9fffc00007fffff8

def z928 : W := mkw 0x22805b1024202e48 0x004500b62048405c 0x6680ff1c3ce07ffd 0xb4cd01fe3879c0ff

def z929 : W := mkw 0xafbad7fea9fee7af 0x0d5f75affd53fdcf 0x1ff8c7fe23ffe3de 0xec3ff18ffc47ffc7

def z930 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x871f07e1c0f87fb9 0x770e3e0fc381f0ff

def z931 : W := mkw 0x2ab6b6d808440000 0x20556d6db0108800 0x669ffffc3ce6007d 0xf4cd3ffff879cc00

def z932 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xf9fff8ffff1ffc77 0xdbf3fff1fffe3ff8

def z933 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x18fffffc00000034 0x6031fffff8000000

def z934 : W := mkw 0x8d36b6d800000000 0x211a6d6db0000000 0x811ffffc00000032 0x63023ffff8000000

def z935 : W := mkw 0x0830c04c20022080 0x0010618098400441 0x19f8c0fe231fe3de 0xec33f181fc463fc7

def z936 : W := mkw 0x500d282356085950 0x12a01a5046ac10b2 0xe11f38e3dc187ffb 0xffc23e71c7b830ff

def z937 : W := mkw 0xfff6b6d880900000 0x23ffed6db1012000 0xfffffffc00f8003f 0xe7fffffff801f000

def z938 : W := mkw 0x7ab4b25800000000 0x02f56964b0000000 0xfffffffc0000003f 0xe3fffffff8000000

def z939 : W := mkw 0x581de82377087970 0x12b03bd046ee10f2 0xf9fff8e3ff1fffff 0xfff3fff1c7fe3fff

def z940 : W := mkw 0xfff6b6d888d50000 0x23ffed6db111aa00 0xfffffffc3cff807f 0xf7fffffff879ff00

def z941 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xfff800e3ffff805f 0xfffff001c7ffff00

def z942 : W := mkw 0x00005b1424222eca 0x040000b62848445d 0x6600ff1c3ce07ffd 0xb4cc01fe3879c0ff

def z943 : W := mkw 0x2282169000000000 0x0045042d20000000 0x669ffffc0000003d 0xe0cd3ffff8000000

def z944 : W := mkw 0x5835e84d7702b8f1 0x12b06bd09aee0571 0xf8e7f81dff079c25 0x13f1cff03bfe0f38

def z945 : W := mkw 0x2ab6b6d800000000 0x20556d6db0000000 0x609ffffc00000034 0x60c13ffff8000000

def z946 : W := mkw 0xf7c636919ad50000 0x23ef8c6d2335aa00 0xffe7ff1fffff807f 0xbfffcffe3fffff00

def z947 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffc2006007f 0xe7fffffff8400c00

def z948 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x861f07e1c0e07ff9 0xf70c3e0fc381c0ff

def z949 : W := mkw 0xa782179488f6068e 0x0d4f042f2911ec0d 0x0680071c00e60388 0x240d000e3801cc07

def z950 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xe0073801dc007c71 0x93c00e7003b800f8

def z951 : W := mkw 0xdd7fa4ebd2995104 0x2bbaff49d7a532a2 0x997f00e3c3198002 0x4b32fe01c7863300

def z952 : W := mkw 0x583de84b7700f871 0x12b07bd096ee01f0 0xf87ff803ff01fc77 0xdbf0fff007fe03f8

def z953 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xe7fffffc00000039 0x63cffffff8000000

def z954 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x19f8c0fe231fe396 0x6833f181fc463fc7

def z955 : W := mkw 0xa7e217f888fd070c 0x294fc42ff111fa0e 0x07e007fc00ff8388 0x240fc00ff801ff07

def z956 : W := mkw 0x7af4fa5d3f4628f2 0x36f5e9f4ba7e8c51 0x78e0f81c3f060004 0x00f1c1f0387e0c00

def z957 : W := mkw 0x500d680377007870 0x12a01ad006ee00f0 0xe007f803ff007c75 0x9bc00ff007fe00f8

def z958 : W := mkw 0x5815e80177003870 0x12b02bd002ee0070 0xf81ff801ff001c37 0xd3f03ff003fe0038

def z959 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x19fffffe231f807e 0xec33fffffc463f00

def z960 : W := mkw 0x5815e80177003870 0x12b02bd002ee0070 0xe007f801dc001c21 0x13c00ff003b80038

def z961 : W := mkw 0x581da00352005000 0x02b03b4006a400a0 0xf81ff803ff007c77 0xdbf03ff007fe00f8

def z962 : W := mkw 0x583da86b5708d971 0x12b07b50d6ae11b2 0xf97f38e3df199c23 0x5bf2fe71c7be3338

def z963 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xfffffffdffe7803f 0xf3fffffffbffcf00

def z964 : W := mkw 0x5815a80156001850 0x12b02b5002ac0030 0xe01ff801dc001c31 0x53c03ff003b80038

def z965 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6600ff1c3ce67ff1 0x34cc01fe3879ccff

def z966 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xf9e00003ffff8046 0x1ff3c00007ffff00

def z967 : W := mkw 0xfff6b6d888d50000 0x23ffed6db111aa00 0xfffffffe23ff807f 0xeffffffffc47ff00

def z968 : W := mkw 0xff96b69000000000 0x03ff2d6d20000000 0xff9ffffc0000003f 0xe3ff3ffff8000000

def z969 : W := mkw 0xa78a57b6a8fe678e 0x0d4f14af6d51fccf 0x0798c7fe20fe63de 0xec0f318ffc41fcc7

def z970 : W := mkw 0x8d36b6d800000000 0x211a6d6db0000000 0x861ffffc00000031 0x630c3ffff8000000

def z971 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x19e0c0fe231fe3cc 0x2c33c181fc463fc7

def z972 : W := mkw 0x5836b6d800000000 0x22b06d6db0000000 0xe01ffffc00000031 0x63c03ffff8000000

def z973 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6600ff1c1ce07ff9 0xb4cc01fe3839c0ff

def z974 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf81f3803ff007c63 0x5bf03e7007fe00f8

def z975 : W := mkw 0x581de827770af9f1 0x12b03bd04eee15f3 0xf9fff803ff1fffff 0xdff3fff007fe3fff

def z976 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x871f07e3c0f87fb3 0x7b0e3e0fc781f0ff

def z977 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xff7ffffc00000033 0x63fefffff8000000

def z978 : W := mkw 0x850000019ad50000 0x010a00000335aa00 0x9fe00003ffff804f 0x9f3fc00007ffff00

def z979 : W := mkw 0xaff6b6d800000000 0x215fed6db0000000 0x1ffffffc0000003e 0xe03ffffff8000000

def z980 : W := mkw 0xa7c000019ad50000 0x014f80000335aa00 0x1fe00003ffff804e 0x9c3fc00007ffff00

def z981 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x79f8c0fe3f1fe3df 0xfcf3f181fc7e3fc7

def z982 : W := mkw 0x00084026200a6180 0x000010804c4014c3 0x19f8c0fe231fe3de 0xec33f181fc463fc7

def z983 : W := mkw 0x0839c06e610af1a1 0x00107380dcc215e3 0x99ffc0ffe31fe3de 0xef33ff81ffc63fc7

def z984 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xe01f3801dc001c33 0xd3c03e7003b80038

def z985 : W := mkw 0x581de827770a79f0 0x12b03bd04eee14f3 0xf99ff8ffff1e7fff 0xfff33ff1fffe3cff

def z986 : W := mkw 0x587de84b77007870 0x32b0fbd096ee00f0 0xf87ff803ff007c77 0xdbf0fff007fe00f8

def z987 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf81ff803df007c33 0x5bf03ff007be00f8

def z988 : W := mkw 0xfff6b6d992910000 0x23ffed6db3252200 0xffffffffc3f9807f 0xffffffffff87f300

def z989 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0xe680ff1ffce67fff 0xbfcd01fe3ff9ccff

def z990 : W := mkw 0xfff6b6d912000000 0x23ffed6db2240000 0xffffffffc300003f 0xebffffffff860000

def z991 : W := mkw 0xfff6b6d888d50000 0x23ffed6db111aa00 0xffffffffc0ff807f 0xffffffffff81ff00

def z992 : W := mkw 0x8502169000000000 0x010a042d20000000 0x871ffffc0000003b 0xe30e3ffff8000000

def z993 : W := mkw 0xfff6b6d801008021 0x23ffed6db0020100 0xfffffffc0301803f 0xe3fffffff8060300

def z994 : W := mkw 0x0001080044001840 0x0000021000880030 0xe0073801dc001c21 0x13c00e7003b80038

def z995 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x871f07e1c0e07fbb 0xf30e3e0fc381c0ff

def z996 : W := mkw 0x2ab6b6d800000000 0x20556d6db0000000 0x7ffffffc0000003f 0xe0fffffff8000000

def z997 : W := mkw 0x8d36b6d800000000 0x211a6d6db0000000 0x9ffffffc0000003f 0xe33ffffff8000000

def z998 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffc00007c7f 0xf3fffffff80000f8

def z999 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x861f07e3c0e07ff3 0xfb0c3e0fc781c0ff

def z1000 : W := mkw 0x583de84f7702f8f1 0x12b07bd09eee05f1 0xf81ff81fff007c77 0xdbf03ff03ffe00f8

def z1001 : W := mkw 0x0830c06c210aa1a1 0x00106180d8421543 0x19e0c0fc231fe3dc 0xa433c181f8463fc7

def z1002 : W := mkw 0x2af6b6d800000000 0x2055ed6db0000000 0x00fffffc00000030 0x6001fffff8000000

def z1003 : W := mkw 0xdd36b6d800000000 0x23ba6d6db0000000 0xff1ffffc0000003f 0xe3fe3ffff8000000

def z1004 : W := mkw 0xdd76b6d800000000 0x23baed6db0000000 0x801ffffc00000030 0x63003ffff8000000

def z1005 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf81ff803ff007fff 0xfff03ff007fe00ff

def z1006 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x871f07e3c0f87fba 0x6f0e3e0fc781f0ff

def z1007 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfefffffc00000035 0x63fdfffff8000000

def z1008 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf81ff803ff007c36 0x4bf03ff007fe00f8

def z1009 : W := mkw 0x000000019ad50000 0x000000000335aa00 0x18e00003ffff8044 0x1c31c00007ffff00

def z1010 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xe01ff803dc007c73 0xdbc03ff007b800f8

def z1011 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x19f8c0fe031fe39a 0x6c33f181fc063fc7

def z1012 : W := mkw 0x5815e80176003850 0x12b02bd002ec0070 0xf81ff801fc007c77 0xd3f03ff003f800f8

def z1013 : W := mkw 0x0838806e010ac1a1 0x00107100dc021583 0x19f800fe031fe3da 0xec33f001fc063fc7

def z1014 : W := mkw 0x583de84b77007870 0x12b07bd096ee00f0 0xf97ff8e3ff007c77 0xdbf2fff1c7fe00f8

def z1015 : W := mkw 0x2280131008640608 0x004500262010c80c 0x6680ff1c3ce67ffd 0xb4cd01fe3879ccff

def z1016 : W := mkw 0x0001480064003840 0x0000029000c80070 0xe007f801fc007c75 0x93c00ff003f800f8

def z1017 : W := mkw 0x0009480377007870 0x1000129006ee00f0 0xe01ff803ff007c77 0xdbc03ff007fe00f8

def z1018 : W := mkw 0x500d680377007870 0x12a01ad006ee00f0 0xf8073803ff007c67 0x9bf00e7007fe00f8

def z1019 : W := mkw 0xfff6b6d992910000 0x23ffed6db3252200 0xffffffffe31f807f 0xefffffffffc63f00

def z1020 : W := mkw 0x22805b142d66aeeb 0x044500b6285acd5d 0x6680ff1c3fe7fffd 0xb4cd01fe387fcfff

def z1021 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xfe1fff03ff007c7f 0xfbfc3ffe07fe00f8

def z1022 : W := mkw 0x500d280357005870 0x12a01a5006ae00b0 0xe0073803df001c21 0x1bc00e7007be0038

def z1023 : W := mkw 0x0009080244005840 0x00001210048800b0 0xe01f3803dc007c73 0xdbc03e7007b800f8

def z1024 : W := mkw 0xa782179088f4060e 0x0d4f042f2111e80c 0x0600070000e00000 0x000c000e0001c000

def z1025 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf91ff8e3ff007c7f 0xfbf23ff1c7fe00f8

def z1026 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x19f8c0fe231f838e 0x6c33f181fc463f07

def z1027 : W := mkw 0x083de06e610af1b1 0x10107bc0dcc215e3 0x19ffc0fe231fe3de 0xec33ff81fc463fc7

def z1028 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xf8073803df001c23 0x1bf00e7007be0038

def z1029 : W := mkw 0xd54000019ad50000 0x03aa80000335aa00 0x99e00003ffff804e 0x9f33c00007ffff00

def z1030 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x011ffffc0000003a 0xe0023ffff8000000

def z1031 : W := mkw 0x0838806e010ac1a1 0x00107100dc021583 0x19f800fe231f83ce 0xec33f001fc463f07

def z1032 : W := mkw 0xaff6b6d800000000 0x215fed6db0000000 0x87fffffc0000003b 0xe30ffffff8000000

def z1033 : W := mkw 0x5836b6d912000000 0x22b06d6db2240000 0xf81fffffff000077 0xfbf03ffffffe0000

def z1034 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xffe0c01fffff805f 0xbfffc1803fffff00

def z1035 : W := mkw 0x2ab6b6d800000000 0x20556d6db0000000 0x069ffffc00000038 0x600d3ffff8000000

def z1036 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x871f07e3e3fffffb 0xff0e3e0fc7c7ffff

def z1037 : W := mkw 0x7af6b6d800000000 0x22f5ed6db0000000 0x7efffffc0000003d 0xe0fdfffff8000000

def z1038 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x861f07e3c0f87ff1 0x7f0c3e0fc781f0ff

def z1039 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x99f8c0ffe31fe3df 0xff33f181ffc63fc7

def z1040 : W := mkw 0xa7e217fc88fe078e 0x2d4fc42ff911fc0f 0x07e007fc00fe0388 0x240fc00ff801fc07

def z1041 : W := mkw 0x581da80357005870 0x12b03b5006ae00b0 0xf81f3803df007c73 0xdbf03e7007be00f8

def z1042 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffc3c00007f 0xf3fffffff8780000

def z1043 : W := mkw 0x85030580c0b0160c 0x090a060b0181602c 0x871f07e1c0e07ffb 0xf70e3e0fc381c0ff

def z1044 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6680ff1c3ce67fb5 0x30cd01fe3879ccff

def z1045 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x79f8f8fe231fe3ff 0xecf3f1f1fc463fc7

def z1046 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf81ff803ff007c46 0x5bf03ff007fe00f8

def z1047 : W := mkw 0x7af6b6d91a450000 0x22f5ed6db2348a00 0x78fffffc3f078034 0x60f1fffff87e0f00

def z1048 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xe0073803dc001c63 0x9bc00e7007b80038

def z1049 : W := mkw 0x583de84f7702f8f1 0x12b07bd09eee05f1 0xf9fff81fff1ffc7f 0xdff3fff03ffe3ff8

def z1050 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x871f07e3c0f87fe3 0x5f0e3e0fc781f0ff

def z1051 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x9f1f07e3e3f87fff 0xff3e3e0fc7c7f0ff

def z1052 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf807f803ff007c65 0x1bf00ff007fe00f8

def z1053 : W := mkw 0x0838c86e250ae9e1 0x00107190dc4a15d3 0x19f8c0fe3f1fffde 0xfc33f181fc7e3fff

def z1054 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x801ffffc00000033 0xe3003ffff8000000

def z1055 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffc00000027 0x43fffffff8000000

def z1056 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xf8fff8ffff07fff7 0xfbf1fff1fffe0fff

def z1057 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x1ff8c7fe231fe3ff 0xec3ff18ffc463fc7

def z1058 : W := mkw 0x0830c06c210aa1a1 0x00106180d8421543 0x19f8c0fc231f839e 0xe433f181f8463f07

def z1059 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6680ff1c1ce07fbd 0xb0cd01fe3839c0ff

def z1060 : W := mkw 0xa7894926ecfe7fce 0x0d4f12924dd9fcff 0xe7800003fcfe7fcf 0x9fcf000007f9fcff

def z1061 : W := mkw 0x00094927feff7fce 0x0c0012924ffdfeff 0x00000003ffffffc0 0x1c00000007ffffff

def z1062 : W := mkw 0xfff6b6d992910000 0x23ffed6db3252200 0xfffffffdc000003f 0xe3fffffffb800000

def z1063 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x181ffffc00000036 0xe0303ffff8000000

def z1064 : W := mkw 0xaff6b6d800000000 0x215fed6db0000000 0x67fffffc0000003d 0xe0cffffff8000000

def z1065 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffe0319803f 0xebfffffffc063300

def z1066 : W := mkw 0xfff6b6d91a450000 0x23ffed6db2348a00 0xfffffffe3f1f807f 0xeffffffffc7e3f00

def z1067 : W := mkw 0x583de86b7708f971 0x12b07bd0d6ee11f2 0xf97ff8e3ff19ffff 0xfff2fff1c7fe33ff

def z1068 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xf89ff8ffff067fff 0xfff13ff1fffe0cff

def z1069 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xffff0003ffff807f 0xdffffe0007ffff00

def z1070 : W := mkw 0x083de86e650af9f1 0x10107bd0dcca15f3 0x79fff8fe3f1fffff 0xfcf3fff1fc7e3fff

def z1071 : W := mkw 0x2ab6b6d800000000 0x20556d6db0000000 0x661ffffc00000031 0x60cc3ffff8000000

def z1072 : W := mkw 0x0836b6d800000000 0x20106d6db0000000 0x197ffffc00000032 0x6032fffff8000000

def z1073 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x67e0ff1c3cfffffd 0xb4cfc1fe3879ffff

def z1074 : W := mkw 0x500d280356005850 0x12a01a5006ac00b0 0xe0073803dc007c61 0x1bc00e7007b800f8

def z1075 : W := mkw 0x581de807770278f0 0x12b03bd00eee04f1 0xf9fff81fff1fffff 0xfff3fff03ffe3fff

def z1076 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xfffffffe2300007f 0xebfffffffc460000

def z1077 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xffe00003ffff800e 0x0fffc00007ffff00

def z1078 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf81ff801ff007c35 0x53f03ff003fe00f8

def z1079 : W := mkw 0xf7c94927feff7fce 0x0fef92924ffdfeff 0xffe00003ffffffcf 0x9fffc00007ffffff

def z1080 : W := mkw 0xf7c012119ad50000 0x03ef80242335aa00 0xffe0071fffff804f 0xbfffc00e3fffff00

def z1081 : W := mkw 0xfff6b6d91a440000 0x23ffed6db2348800 0xffffffffffe6007f 0xffffffffffffcc00

def z1082 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xfe1ff803ffe07c7f 0xdffc3ff007ffc0f8

def z1083 : W := mkw 0x5005680176003850 0x12a00ad002ec0070 0xe007f801fc001c25 0x13c00ff003f80038

def z1084 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xf97ff8ffff19fff7 0xfbf2fff1fffe33ff

def z1085 : W := mkw 0x083bdffe652affef 0x0c1077bffcca55ff 0x001ffffc00007fb0 0x60003ffff80000ff

def z1086 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0xfee00003ffff8045 0x1ffdc00007ffff00

def z1087 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x19f800fe231fe3ca 0x6c33f001fc463fc7

def z1088 : W := mkw 0xf7c000019ad50000 0x03ef80000335aa00 0x9fe00003ffff804a 0x1f3fc00007ffff00

def z1089 : W := mkw 0x7ab6b6d800000000 0x22f56d6db0000000 0xfe9ffffc0000003f 0xe3fd3ffff8000000

def z1090 : W := mkw 0x8d36b6d800000000 0x211a6d6db0000000 0x071ffffc00000038 0x600e3ffff8000000

def z1091 : W := mkw 0xa780000088d40000 0x014f00000111a800 0xffe00003ffff804f 0x9fffc00007ffff00

def z1092 : W := mkw 0x581de8237708f971 0x12b03bd046ee11f2 0xf81ff803ff19fc77 0xdbf03ff007fe33f8

def z1093 : W := mkw 0xfff6b6d91a450000 0x23ffed6db2348a00 0xfffffffc1c00003f 0xe3fffffff8380000

def z1094 : W := mkw 0x0002169000000000 0x0000042d20000000 0x001ffffc00000030 0x60003ffff8000000

def z1095 : W := mkw 0xfff6b6d992910000 0x23ffed6db3252200 0xffffffffff19807f 0xfbfffffffffe3300

def z1096 : W := mkw 0x583de84b77007870 0x12b07bd096ee00f0 0xf8fff81fff007c77 0xdbf1fff03ffe00f8

def z1097 : W := mkw 0x581de8077702f8f1 0x12b03bd00eee05f1 0xf81ff803ff07fc77 0xdbf03ff007fe0ff8

def z1098 : W := mkw 0x7af6b6d800000000 0x22f5ed6db0000000 0xf8fffffc00000037 0xe3f1fffff8000000

def z1099 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xf91ff8ffff187fff 0xfff23ff1fffe30ff

def z1100 : W := mkw 0x583de86f770af9f1 0x12b07bd0deee15f3 0xf9fff8ffff007fff 0xfbf3fff1fffe00ff

def z1101 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xe01ff801fc007c75 0xd3c03ff003f800f8

def z1102 : W := mkw 0xafb6b6d800000000 0x215f6d6db0000000 0xe79ffffc0000003f 0xe3cf3ffff8000000

def z1103 : W := mkw 0x00094926edfeffef 0x0c0012924ddbfdff 0x00000003ffffffc0 0x1c00000007ffffff

def z1104 : W := mkw 0x228000019ad50000 0x004500000335aa00 0x7fe00003ffff804f 0x9cffc00007ffff00

def z1105 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x7ee0ff1c3fe7fffd 0xb4fdc1fe387fcfff

def z1106 : W := mkw 0x7af6b6d800000000 0x22f5ed6db0000000 0x79fffffc0000003e 0xe0f3fffff8000000

def z1107 : W := mkw 0x0838c06e210ae1a1 0x00107180dc4215c3 0x1ff8c0fe23ffe3df 0xfc3ff181fc47ffc7

def z1108 : W := mkw 0x0838c86e250ae9e1 0x00107190dc4a15d3 0x19f8f8fe231ffffe 0xec33f1f1fc463fff

def z1109 : W := mkw 0xfff6b6d808440000 0x23ffed6db0108800 0xfffffffc00e6003f 0xe7fffffff801cc00

def z1110 : W := mkw 0xfff6b6d91a450000 0x23ffed6db2348a00 0xfffffffc3fe7807f 0xf7fffffff87fcf00

def z1111 : W := mkw 0x500d280356005850 0x12a01a5006ac00b0 0xe01f3801dc007c31 0x53c03e7003b800f8

def z1112 : W := mkw 0x5835a84956001850 0x12b06b5092ac0030 0xf9fff8fddc001c3f 0xf3f3fff1fbb80038

def z1113 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x7fe0ff1c3ce67fff 0xb4ffc1fe3879ccff

def z1114 : W := mkw 0x0839c06e610af1a1 0x00107380dcc215e3 0x19ffc0fe231ffffe 0xec33ff81fc463fff

def z1115 : W := mkw 0x22805b142c662eca 0x044500b62858cc5d 0x6680ff1c3ce67fcc 0x34cd01fe3879ccff

def z1116 : W := mkw 0x5005680177003870 0x12a00ad002ee0070 0xe0073801ff001c21 0x13c00e7003fe0038

def z1117 : W := mkw 0x581de80377007870 0x12b03bd006ee00f0 0xf89ff81fff007c7f 0xfbf13ff03ffe00f8

def z1118 : W := mkw 0xa7c217b488ff078e 0x0d4f842f6911fe0f 0x07e007fc00ff8388 0x240fc00ff801ff07

def z1119 : W := mkw 0x083ce86e250ae9f1 0x101079d0dc4a15d3 0x19f8f8fe231fe3de 0xec33f1f1fc463fc7

def z1120 : W := mkw 0x083de86e650af9f1 0x10107bd0dcca15f3 0x99fff8ffe31fffff 0xff33fff1ffc63fff

def z1121 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0xe71ffffc0000003b 0xe3ce3ffff8000000

def z1122 : W := mkw 0x5005280156001850 0x12a00a5002ac0030 0xf8073801ff001c25 0x13f00e7003fe0038

def z1123 : W := mkw 0x850b05a2c0b8570c 0x090a160b458170ae 0x879f07e3e0fe7fff 0xff0f3e0fc7c1fcff

def z1124 : W := mkw 0xdd76b6d800000000 0x23baed6db0000000 0x99fffffc0000003e 0xe333fffff8000000

def z1125 : W := mkw 0xfff6b6d880910000 0x23ffed6db1012200 0xfffffffc0019803f 0xe3fffffff8003300

def z1126 : W := mkw 0xdd76b6d992910000 0x23baed6db3252200 0x997fffffc3198032 0x6b32ffffff863300

def z1127 : W := mkw 0xfff6b6d99ad50000 0x23ffed6db335aa00 0xfffffffc3fff803f 0xe7fffffff87fff00

def z1128 : W := mkw 0xfff6b6d800000000 0x23ffed6db0000000 0x7ffffffc0000003c 0x60fffffff8000000

def z1129 : W := mkw 0x581de807770278f0 0x12b03bd00eee04f1 0xf81ff81fff007ff7 0xfbf03ff03ffe00ff

def z1130 : W := mkw 0x850b058240205608 0x010a160b048040ac 0x871f07e3c0e07ffb 0xff0e3e0fc781c0ff

def z1131 : W := mkw 0x5836b6d800000000 0x22b06d6db0000000 0x781ffffc00000034 0x60f03ffff8000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z7,z6])],[(0,[z0,z2,z8,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z5,z6]),(0,[z11,z0,z2,z3,z12,z4,z5]),(1,[z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z14,z3,z4,z5,z6])],[(0,[z0,z2,z3,z15,z4,z5,z6]),(0,[z16,z0,z2,z3,z4,z5,z6])],[(1,[z17,z2,z3,z4,z5,z6]),(0,[z18,z0,z19,z3,z4,z5,z6]),(0,[z0,z2,z3,z20,z4,z5,z6])],[(0,[z0,z2,z9,z4,z21,z5,z6]),(0,[z0,z22,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z4,z24,z5,z6]),(0,[z25,z0,z2,z26,z4,z5,z6]),(0,[z0,z2,z3,z4,z27,z5,z6]),(0,[z28,z0,z2,z3,z4,z5,z6]),(1,[z29,z0,z2,z21,z5,z6]),(0,[z0,z2,z3,z4,z5,z30,z6]),(0,[z11,z0,z2,z3,z31,z4,z5])],[(0,[z0,z2,z3,z4,z5,z32,z6]),(0,[z0,z2,z3,z4,z33,z5,z6]),(0,[z0,z34,z2,z35,z4,z5,z6]),(0,[z0,z2,z3,z36,z4,z5,z6]),(0,[z37,z11,z0,z2,z3,z4,z6])],[(0,[z0,z2,z23,z38,z4,z5,z6]),(0,[z0,z2,z3,z4,z39,z40,z5]),(0,[z0,z2,z3,z41,z4,z5,z6]),(0,[z0,z2,z3,z42,z4,z5,z6]),(0,[z43,z0,z2,z3,z44,z5,z6]),(0,[z0,z2,z45,z3,z4,z5,z6])],[(0,[z0,z2,z3,z9,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z46,z5])]],
   [[(0,[z47,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z48,z4,z5,z6]),(0,[z2,z3,z4,z49,z5,z6,z50]),(0,[z0,z51,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z52,z4,z5,z6]),(0,[z29,z53,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z54]),(0,[z55,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z56]),(0,[z0,z2,z3,z4,z5,z6,z57]),(0,[z58,z0,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z59,z5]),(0,[z0,z2,z60,z3,z4,z5,z6])],[(0,[z0,z61,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z62,z5,z6]),(0,[z63,z0,z2,z3,z4,z5,z6]),(0,[z64,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z65,z5,z6]),(0,[z66,z0,z2,z3,z4,z5,z6]),(0,[z67,z11,z0,z2,z3,z4,z5])],[(0,[z0,z34,z2,z9,z4,z5,z6]),(1,[z68,z2,z3,z4,z5,z69]),(0,[z0,z34,z35,z3,z4,z5,z6]),(0,[z11,z0,z70,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z6,z50]),(0,[z71,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z72,z6]),(0,[z11,z0,z2,z3,z73,z4,z5])],[(0,[z74,z0,z2,z3,z4,z5,z6]),(1,[z2,z8,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z75,z5,z6]),(0,[z76,z2,z3,z4,z77,z5,z6]),(0,[z0,z2,z3,z78,z4,z5,z6]),(0,[z0,z2,z79,z3,z4,z5,z6])],[(0,[z0,z2,z23,z4,z5,z80,z6]),(0,[z29,z0,z2,z23,z4,z5,z6]),(0,[z0,z81,z2,z3,z4,z5,z6]),(0,[z0,z82,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z83,z5,z6]),(0,[z11,z0,z2,z84,z3,z4,z5])]],
   [[(0,[z0,z2,z3,z85,z4,z5,z6]),(0,[z86,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z87,z6]),(0,[z0,z2,z88,z3,z4,z5,z6])],[(0,[z89,z0,z2,z3,z4,z5,z90]),(0,[z91,z0,z2,z3,z4,z5,z90]),(0,[z92,z0,z2,z3,z77,z5,z6]),(0,[z0,z2,z3,z4,z5,z93,z6]),(0,[z0,z2,z3,z4,z94,z5,z6]),(0,[z95,z0,z2,z3,z4,z5,z6])],[(0,[z2,z3,z12,z4,z77,z5,z6])],[(0,[z96,z0,z2,z3,z4,z5,z6]),(0,[z0,z34,z2,z73,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z97,z6]),(0,[z0,z2,z3,z4,z5,z6,z98]),(0,[z0,z2,z3,z4,z21,z5,z90]),(0,[z0,z2,z3,z99,z4,z5,z90]),(0,[z0,z2,z100,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z5,z90])],[(0,[z91,z0,z2,z9,z4,z5,z6]),(0,[z101,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z102]),(0,[z0,z2,z9,z4,z103,z5,z6]),(0,[z0,z2,z23,z104,z4,z5,z6]),(0,[z105,z0,z2,z3,z4,z6,z90]),(0,[z106,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z107,z3,z4,z5,z6])],[(0,[z89,z11,z0,z2,z3,z4,z5]),(0,[z91,z11,z0,z2,z3,z4,z5]),(1,[z108,z0,z2,z3,z4,z90]),(0,[z68,z0,z2,z3,z4,z5,z109]),(0,[z110,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z111,z5,z6])],[(0,[z0,z2,z3,z112,z4,z5,z6]),(1,[z0,z22,z3,z78,z5,z6]),(0,[z55,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z113,z4,z5,z6]),(0,[z0,z2,z114,z3,z4,z5,z6]),(0,[z0,z115,z2,z3,z4,z5,z90])]],
   [[(1,[z0,z2,z116,z4,z5,z6]),(0,[z117,z0,z2,z3,z4,z5,z6]),(0,[z0,z118,z2,z3,z4,z5,z6]),(0,[z119,z0,z2,z3,z4,z5,z90]),(0,[z11,z11,z0,z2,z3,z4,z5])],[(0,[z120,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z121,z4,z5,z6]),(0,[z122,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z123,z6]),(0,[z0,z2,z3,z124,z4,z5,z6])],[(0,[z0,z2,z3,z4,z125,z5,z6]),(0,[z25,z0,z34,z3,z4,z5,z6]),(0,[z25,z0,z3,z26,z4,z5,z6]),(0,[z37,z0,z2,z3,z4,z80,z6]),(0,[z0,z2,z3,z4,z126,z5,z6]),(0,[z0,z2,z4,z127,z5,z6,z128])],[(0,[z0,z2,z9,z4,z129,z5,z6]),(1,[z130,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z131,z5,z6]),(0,[z0,z2,z132,z3,z4,z5,z6])],[(0,[z0,z133,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z134,z6]),(0,[z0,z2,z3,z135,z4,z5,z6]),(0,[z0,z2,z3,z4,z136,z5,z6]),(0,[z137,z0,z2,z3,z4,z5,z6]),(0,[z138,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z23,z4,z5,z6,z128]),(0,[z29,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z90,z139]),(0,[z0,z2,z3,z4,z140,z5,z6])],[(1,[z0,z2,z3,z4,z141,z6]),(0,[z0,z142,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z26,z4,z5,z6]),(0,[z0,z2,z3,z143,z4,z5,z6]),(0,[z0,z2,z3,z4,z144,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z90]),(0,[z145,z11,z0,z2,z3,z4,z5])],[(0,[z146,z0,z2,z3,z4,z5,z109]),(0,[z147,z0,z2,z3,z4,z5,z6]),(0,[z92,z0,z2,z3,z99,z5,z6]),(0,[z148,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z149,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z150,z151,z4,z6])],[(0,[z0,z2,z3,z4,z152,z5,z6]),(0,[z0,z2,z3,z153,z4,z5,z6]),(0,[z154,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z155,z5,z6])],[(0,[z0,z2,z23,z4,z156,z5,z6]),(0,[z0,z157,z2,z3,z4,z5,z6]),(0,[z158,z11,z0,z2,z3,z4,z5])],[(0,[z159,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z160,z6]),(0,[z0,z2,z23,z35,z4,z5,z6]),(0,[z0,z34,z2,z26,z4,z5,z6]),(0,[z11,z0,z2,z3,z78,z4,z5]),(0,[z11,z0,z161,z2,z3,z4,z5]),(0,[z11,z0,z19,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z162,z5,z6]),(0,[z0,z161,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z163,z6])],[(0,[z0,z2,z3,z164,z4,z5,z6]),(0,[z0,z2,z165,z4,z5,z6,z128])],[(1,[z105,z2,z3,z4,z49,z6]),(0,[z11,z0,z2,z35,z3,z4,z5]),(0,[z0,z166,z2,z3,z4,z5,z6]),(0,[z18,z0,z3,z4,z129,z5,z6])],[(0,[z55,z0,z8,z3,z4,z5,z6]),(0,[z0,z2,z9,z4,z59,z5,z6]),(0,[z0,z2,z23,z3,z4,z5,z90]),(0,[z167,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z168,z4,z5,z6]),(0,[z0,z2,z9,z4,z5,z169,z6]),(0,[z76,z170,z2,z3,z4,z5,z6]),(0,[z108,z0,z2,z3,z4,z6,z50]),(0,[z0,z2,z3,z171,z4,z5,z6]),(0,[z0,z172,z2,z3,z4,z5,z6])],[(0,[z0,z173,z2,z3,z4,z5,z6]),(0,[z174,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z175,z4,z5,z6]),(0,[z25,z0,z2,z35,z4,z5,z6])],[(0,[z0,z2,z3,z176,z4,z5,z6]),(0,[z11,z0,z2,z8,z3,z4,z5]),(0,[z0,z2,z23,z9,z4,z5,z6]),(1,[z0,z2,z177,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z90,z109]),(0,[z0,z2,z3,z4,z5,z6,z178]),(0,[z0,z179,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z156,z5,z180])],[(0,[z0,z2,z3,z4,z5,z181,z6]),(1,[z0,z2,z182,z4,z5,z6]),(1,[z142,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z183,z5,z6]),(0,[z11,z0,z2,z3,z4,z5,z184])],[(0,[z68,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z23,z4,z5,z6,z56]),(0,[z185,z0,z2,z3,z4,z5,z6]),(0,[z186,z0,z2,z3,z4,z5,z6]),(0,[z29,z0,z2,z4,z21,z5,z6]),(0,[z0,z2,z3,z31,z99,z4,z6])],[(0,[z0,z2,z187,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z188,z5,z6]),(0,[z25,z17,z2,z3,z4,z5,z6]),(0,[z189,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z104,z3,z21,z5,z6]),(0,[z0,z2,z104,z3,z4,z5,z90]),(0,[z0,z2,z3,z190,z4,z5,z6]),(0,[z0,z191,z2,z3,z4,z5,z6])],[(0,[z192,z0,z2,z3,z4,z5,z6]),(0,[z193,z0,z2,z3,z4,z5,z6])],[(0,[z89,z0,z2,z194,z4,z5,z6]),(0,[z195,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z196,z4,z5,z6]),(0,[z2,z3,z4,z5,z69,z6,z109]),(0,[z0,z2,z3,z4,z197,z5,z6]),(0,[z198,z0,z2,z4,z46,z5,z6]),(0,[z0,z2,z165,z3,z4,z5,z90])]],
   [[(1,[z89,z8,z3,z4,z5,z6]),(0,[z0,z2,z104,z9,z4,z5,z6]),(0,[z0,z2,z23,z4,z5,z6,z50]),(0,[z11,z0,z2,z3,z4,z5,z69]),(0,[z0,z2,z4,z131,z40,z5,z6]),(0,[z55,z0,z161,z3,z4,z5,z6]),(0,[z0,z199,z2,z3,z4,z5,z6])],[(0,[z0,z200,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z201,z6]),(0,[z0,z2,z23,z78,z4,z5,z6]),(1,[z0,z2,z202,z4,z5,z6]),(0,[z0,z2,z3,z203,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z90,z204]),(0,[z0,z2,z3,z4,z5,z205,z6])],[(0,[z0,z2,z165,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z69,z90])],[(0,[z0,z2,z3,z4,z5,z206,z6]),(0,[z207,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z208,z4,z5,z6]),(1,[z76,z2,z3,z77,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z139])],[(0,[z146,z0,z2,z23,z4,z5,z6]),(0,[z209,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z210,z6]),(0,[z0,z2,z3,z4,z5,z6,z211]),(0,[z130,z0,z2,z4,z40,z5,z6]),(0,[z0,z2,z3,z4,z212,z5,z6]),(0,[z0,z2,z3,z4,z213,z5,z6])],[(0,[z89,z0,z133,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z214,z5,z6]),(0,[z0,z2,z3,z4,z215,z5,z6]),(0,[z0,z2,z3,z4,z5,z184,z6]),(0,[z0,z2,z3,z4,z59,z5,z90])],[(0,[z174,z0,z2,z3,z4,z5,z6]),(1,[z2,z23,z9,z4,z5,z6]),(0,[z76,z0,z2,z216,z4,z5,z6]),(0,[z108,z0,z217,z3,z4,z5,z6]),(0,[z108,z0,z2,z3,z13,z5,z6]),(1,[z0,z2,z3,z4,z5,z218]),(0,[z25,z0,z2,z73,z4,z5,z6]),(0,[z219,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z104,z3,z73,z5,z6]),(0,[z0,z2,z3,z4,z5,z169,z90])]],
   [[(1,[z0,z2,z220,z4,z5,z6]),(0,[z0,z0,z2,z23,z4,z5,z6]),(0,[z221,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z13,z4,z5,z6]),(0,[z0,z2,z222,z3,z4,z5,z6]),(0,[z0,z223,z2,z3,z4,z5,z6]),(0,[z0,z224,z2,z3,z4,z5,z6])],[(0,[z198,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z225,z4,z5,z6]),(0,[z108,z0,z2,z3,z4,z5,z90]),(0,[z0,z226,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z227]),(0,[z0,z2,z3,z4,z228,z5,z6]),(0,[z68,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z129,z5,z6,z56]),(0,[z11,z0,z2,z3,z229,z4,z5])],[(0,[z230,z0,z2,z3,z4,z5,z6]),(1,[z170,z2,z3,z12,z5,z6]),(1,[z0,z231,z3,z4,z5,z6]),(0,[z232,z0,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z5,z128])],[(0,[z0,z2,z3,z4,z233,z5,z6]),(0,[z234,z0,z2,z3,z4,z5,z6]),(0,[z108,z0,z2,z9,z4,z5,z6]),(0,[z235,z0,z2,z3,z4,z5,z6]),(0,[z236,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z46,z5,z6]),(0,[z0,z2,z237,z3,z4,z5,z238])],[(0,[z239,z0,z2,z3,z4,z5,z6]),(1,[z11,z0,z2,z9,z4,z5]),(0,[z0,z2,z237,z23,z4,z5,z6]),(0,[z170,z0,z2,z3,z12,z5,z6]),(0,[z0,z2,z4,z46,z5,z169,z6]),(0,[z0,z2,z3,z240,z4,z5,z6])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z241,z0,z2,z3,z4,z5,z6]),(0,[z108,z0,z2,z3,z4,z49,z6]),(0,[z146,z2,z3,z4,z5,z6,z109]),(1,[z0,z2,z3,z4,z80,z90]),(1,[z53,z2,z3,z4,z5,z6])],[(0,[z91,z242,z2,z3,z4,z5,z6]),(0,[z0,z2,z9,z4,z5,z6,z243]),(1,[z91,z2,z23,z4,z5,z6]),(0,[z170,z0,z2,z3,z4,z5,z90]),(0,[z0,z2,z3,z4,z5,z244,z6]),(0,[z0,z2,z3,z245,z4,z5,z6])]],
   [[(0,[z108,z0,z2,z3,z246,z5,z6]),(0,[z0,z2,z3,z4,z5,z247,z6]),(0,[z248,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z249,z4,z5,z6])],[(0,[z0,z2,z23,z26,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z109]),(0,[z0,z2,z250,z3,z4,z5,z6]),(0,[z53,z0,z2,z3,z4,z5,z6])],[(0,[z251,z0,z2,z3,z4,z5,z6]),(0,[z170,z0,z2,z9,z4,z5,z6]),(0,[z252,z0,z2,z3,z4,z5,z6]),(0,[z130,z0,z2,z3,z4,z5,z6])],[(0,[z146,z0,z2,z3,z4,z5,z6]),(0,[z253,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z254,z5,z6])],[(0,[z0,z255,z2,z3,z4,z5,z6]),(0,[z170,z11,z0,z2,z3,z4,z5]),(1,[z0,z2,z256,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z257]),(0,[z0,z2,z258,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z238]),(0,[z0,z2,z3,z4,z259,z5,z6]),(0,[z0,z2,z3,z260,z4,z5,z6])],[(1,[z0,z2,z23,z4,z5,z6]),(0,[z0,z35,z3,z26,z4,z5,z6]),(0,[z0,z2,z3,z261,z4,z5,z6])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z262,z4,z5,z6]),(0,[z242,z0,z2,z3,z4,z5,z90]),(0,[z0,z263,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z264,z4,z5,z6]),(0,[z0,z265,z2,z3,z4,z5,z6]),(0,[z63,z198,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z266,z5,z6])],[(0,[z0,z2,z3,z4,z40,z5,z6]),(0,[z198,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z267,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z268]),(0,[z269,z0,z2,z3,z40,z5,z6]),(0,[z0,z270,z2,z3,z4,z5,z6]),(1,[z271,z0,z2,z4,z127,z5]),(0,[z272,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z9,z4,z49,z5,z6]),(0,[z91,z2,z3,z4,z49,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z218]),(0,[z0,z2,z273,z3,z4,z5,z6])],[(0,[z108,z2,z3,z9,z4,z5,z6]),(0,[z0,z2,z23,z165,z4,z5,z6]),(0,[z29,z0,z34,z2,z4,z5,z6]),(0,[z274,z0,z2,z3,z4,z5,z6]),(0,[z275,z0,z2,z3,z4,z5,z6])],[(0,[z0,z34,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z12,z4,z5,z6]),(0,[z276,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z237,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z127,z5])],[(0,[z277,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z278,z5,z6]),(0,[z0,z279,z2,z3,z4,z5,z6]),(0,[z0,z19,z2,z3,z4,z280,z6]),(0,[z37,z0,z2,z3,z4,z5,z90])],[(0,[z117,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z281,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z282,z6]),(0,[z11,z0,z2,z165,z3,z4,z5]),(0,[z0,z2,z3,z31,z4,z5,z6])],[(0,[z0,z2,z3,z4,z283,z5,z6]),(0,[z0,z2,z8,z3,z4,z5,z6]),(0,[z0,z2,z23,z4,z5,z181,z6]),(0,[z11,z0,z2,z3,z4,z5,z50]),(0,[z284,z0,z2,z3,z4,z5,z6])],[(0,[z0,z285,z2,z9,z4,z5,z6]),(0,[z92,z0,z2,z3,z12,z5,z6]),(0,[z286,z0,z2,z3,z4,z5,z6]),(0,[z0,z287,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z203,z4,z5]),(0,[z0,z2,z3,z151,z4,z5,z6]),(0,[z11,z0,z2,z3,z151,z4,z5]),(0,[z288,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z289,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z290,z6]),(0,[z105,z0,z2,z3,z4,z6,z50]),(0,[z0,z2,z3,z291,z4,z5,z6]),(0,[z292,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z293,z6])],[(0,[z0,z133,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z73,z4,z5,z6]),(0,[z92,z0,z2,z3,z4,z5,z90]),(0,[z37,z11,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z229,z4,z5,z6])],[(0,[z0,z2,z294,z3,z4,z5,z6]),(0,[z55,z0,z2,z3,z4,z80,z6]),(0,[z0,z19,z2,z3,z4,z295,z6]),(0,[z92,z0,z2,z3,z31,z5,z6]),(0,[z296,z0,z2,z3,z4,z5,z90])],[(1,[z0,z2,z3,z4,z5,z6]),(1,[z0,z19,z3,z4,z5,z56]),(1,[z265,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z297,z0,z2,z9,z4,z5,z6]),(0,[z92,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z184,z6,z90]),(0,[z0,z2,z3,z298,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z299,z6]),(0,[z91,z300,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z301,z5,z6]),(0,[z25,z142,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z302,z5,z6])],[(0,[z11,z242,z0,z2,z3,z4,z5]),(1,[z2,z9,z4,z49,z5,z6]),(0,[z0,z2,z3,z4,z5,z303,z6]),(0,[z0,z2,z3,z4,z5,z6,z238]),(0,[z67,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z99,z184,z6]),(0,[z92,z11,z0,z2,z3,z4,z5])],[(0,[z89,z0,z2,z9,z4,z5,z6]),(0,[z0,z304,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z305,z6]),(0,[z0,z2,z3,z306,z4,z5,z6]),(0,[z18,z0,z2,z3,z4,z5,z90]),(0,[z307,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z165,z3,z4,z5,z128])]],
   [[(0,[z0,z2,z168,z9,z4,z5,z6]),(0,[z0,z2,z9,z4,z5,z6,z128]),(0,[z0,z308,z2,z23,z4,z5,z6]),(0,[z0,z2,z23,z4,z127,z5,z6]),(0,[z0,z2,z3,z4,z49,z5,z90]),(0,[z309,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z310,z4,z5,z6])],[(0,[z0,z2,z311,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z312]),(0,[z11,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z23,z4,z5,z184,z6]),(0,[z0,z34,z2,z3,z4,z5,z6]),(0,[z198,z0,z2,z237,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z313]),(0,[z314,z11,z0,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z6,z315]),(0,[z18,z0,z2,z9,z4,z5,z6]),(0,[z316,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z317,z4,z5,z6]),(0,[z76,z0,z2,z3,z4,z5,z90]),(0,[z0,z2,z3,z4,z318,z5,z6]),(0,[z11,z0,z2,z3,z260,z4,z5])],[(0,[z319,z0,z2,z3,z4,z5,z6]),(0,[z0,z22,z3,z78,z4,z5,z6]),(0,[z320,z0,z2,z3,z4,z5,z6]),(0,[z18,z11,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z321,z6]),(0,[z198,z0,z2,z3,z4,z46,z6]),(0,[z0,z2,z3,z322,z4,z5,z6]),(0,[z0,z2,z3,z203,z99,z4,z5])],[(0,[z0,z2,z323,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z324])],[(0,[z325,z0,z2,z3,z4,z5,z6]),(0,[z76,z0,z2,z9,z4,z5,z6]),(0,[z76,z0,z2,z3,z77,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z326]),(0,[z327,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z328,z3,z4,z5,z6]),(1,[z25,z0,z26,z4,z5,z6]),(0,[z0,z2,z3,z329,z4,z5,z6]),(0,[z0,z2,z3,z4,z330,z5,z6]),(0,[z0,z2,z3,z331,z4,z5,z6])],[(0,[z0,z2,z23,z4,z46,z5,z6]),(0,[z0,z2,z3,z4,z332,z5,z6]),(0,[z0,z2,z3,z333,z4,z5,z6]),(0,[z0,z2,z3,z334,z4,z5,z6]),(0,[z335,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z90,z336])]],
   [[(0,[z76,z11,z0,z2,z3,z4,z5]),(0,[z29,z265,z2,z3,z4,z5,z6]),(0,[z0,z2,z237,z3,z4,z46,z6]),(0,[z198,z0,z2,z3,z4,z169,z6])],[(0,[z108,z0,z2,z182,z4,z5,z6]),(0,[z105,z0,z2,z3,z4,z5,z90])],[(0,[z0,z2,z3,z4,z337,z5,z6]),(1,[z338,z0,z2,z3,z4,z5])],[(0,[z0,z2,z9,z4,z339,z5,z6]),(0,[z0,z22,z2,z3,z40,z5,z6]),(0,[z0,z2,z3,z4,z156,z6,z90]),(0,[z0,z2,z3,z4,z21,z5,z6]),(0,[z0,z2,z3,z4,z340,z5,z6]),(0,[z0,z2,z3,z99,z4,z5,z6])],[(0,[z0,z2,z23,z4,z5,z6,z109]),(1,[z0,z2,z341,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z342,z6]),(0,[z17,z0,z2,z3,z4,z5,z6]),(0,[z343,z0,z2,z3,z4,z5,z6]),(0,[z269,z0,z2,z3,z4,z5,z90]),(0,[z0,z2,z237,z3,z4,z169,z6]),(0,[z37,z0,z2,z3,z4,z184,z6]),(0,[z0,z2,z3,z44,z5,z6,z204]),(0,[z11,z0,z2,z344,z3,z4,z5])],[(0,[z0,z345,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z346,z5,z6]),(0,[z0,z2,z9,z9,z4,z5,z6]),(0,[z0,z2,z347,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z348]),(0,[z0,z2,z3,z4,z5,z6,z6])],[(0,[z0,z2,z9,z48,z4,z5,z6]),(0,[z0,z308,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z77,z5,z6]),(0,[z349,z0,z2,z3,z4,z5,z6])],[(0,[z108,z0,z2,z202,z4,z5,z6]),(0,[z0,z2,z3,z350,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z351,z6]),(0,[z0,z2,z165,z3,z4,z127,z5]),(0,[z0,z2,z344,z3,z4,z5,z6])]],
   [[(0,[z352,z0,z2,z3,z4,z5,z6]),(0,[z353,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z104,z73,z5,z6]),(0,[z119,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z23,z23,z4,z5,z6]),(0,[z0,z2,z3,z354,z4,z5,z6]),(0,[z269,z11,z0,z2,z3,z4,z5]),(0,[z145,z0,z2,z3,z4,z5,z6]),(0,[z92,z0,z2,z3,z4,z184,z6])],[(0,[z0,z2,z3,z355,z4,z5,z6]),(0,[z0,z2,z23,z4,z40,z5,z6]),(0,[z0,z2,z356,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z246,z5,z6]),(0,[z0,z3,z4,z156,z5,z80,z6]),(0,[z0,z2,z3,z357,z4,z5,z6]),(0,[z271,z0,z2,z3,z4,z5,z90])],[(0,[z242,z0,z133,z3,z4,z5,z6]),(0,[z358,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z359,z5,z6]),(0,[z360,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z9,z78,z4,z5,z6]),(0,[z11,z0,z2,z23,z3,z4,z5]),(0,[z108,z37,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z361,z6])],[(0,[z271,z0,z2,z9,z4,z5,z6]),(0,[z108,z0,z2,z3,z4,z5,z218]),(0,[z0,z161,z2,z3,z4,z80,z6]),(0,[z0,z2,z3,z4,z129,z5,z90]),(0,[z158,z0,z2,z3,z4,z5,z6]),(0,[z0,z362,z2,z3,z4,z5,z6])],[(0,[z0,z2,z23,z12,z4,z5,z6]),(0,[z0,z2,z177,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z5,z80]),(0,[z0,z2,z3,z4,z363,z5,z6]),(0,[z364,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z365,z5,z6]),(0,[z0,z2,z3,z31,z4,z6,z90])],[(0,[z0,z366,z2,z3,z4,z5,z6]),(0,[z2,z3,z9,z4,z77,z5,z6]),(0,[z25,z0,z2,z23,z4,z5,z6]),(1,[z269,z0,z3,z40,z5,z6]),(0,[z271,z11,z0,z2,z3,z4,z5])]],
   [[(0,[z0,z2,z9,z44,z4,z5,z6]),(0,[z0,z2,z23,z31,z4,z5,z6]),(0,[z0,z2,z3,z367,z4,z5,z6]),(0,[z368,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z20,z4,z5,z90])],[(0,[z0,z2,z3,z4,z369,z5,z6]),(0,[z108,z0,z231,z3,z4,z5,z6]),(0,[z0,z2,z3,z370,z4,z5,z6])],[(0,[z0,z2,z371,z3,z4,z5,z6]),(0,[z0,z2,z23,z151,z4,z5,z6]),(1,[z18,z0,z3,z4,z129,z5])],[(0,[z372,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z373,z6]),(1,[z0,z2,z9,z4,z5,z90]),(0,[z0,z2,z9,z4,z5,z6,z90]),(0,[z0,z2,z374,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z21,z5]),(0,[z11,z0,z2,z3,z4,z5,z169])],[(0,[z0,z2,z3,z4,z5,z6,z375]),(0,[z0,z2,z121,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z103,z5,z6]),(0,[z0,z2,z23,z73,z4,z5,z6]),(0,[z0,z2,z376,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z49,z5,z377]),(0,[z0,z161,z2,z3,z4,z5,z378]),(0,[z379,z0,z2,z3,z4,z5,z6]),(0,[z0,z19,z2,z3,z4,z5,z90]),(0,[z0,z2,z3,z4,z380,z5,z6])],[(0,[z0,z2,z3,z202,z4,z5,z6]),(1,[z0,z2,z3,z151,z5,z204]),(0,[z0,z2,z3,z151,z4,z5,z204]),(0,[z0,z2,z3,z381,z4,z5,z90])],[(0,[z68,z2,z3,z4,z5,z69,z6]),(0,[z0,z2,z3,z4,z5,z6,z336])],[(0,[z0,z2,z23,z3,z4,z5,z6]),(0,[z0,z19,z2,z9,z4,z5,z6]),(0,[z146,z0,z2,z256,z4,z5,z6]),(0,[z0,z382,z2,z3,z4,z5,z6]),(0,[z383,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z384]),(0,[z385,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z386,z5,z6]),(0,[z387,z0,z2,z3,z4,z5,z6]),(0,[z0,z388,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z113,z4,z46,z5]),(0,[z0,z2,z3,z4,z127,z5,z6])],[],[(0,[z389,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z390,z5,z6]),(1,[z0,z2,z391,z4,z5,z6]),(0,[z0,z2,z3,z4,z392,z5,z6]),(0,[z0,z393,z2,z3,z4,z5,z6]),(0,[z0,z2,z104,z73,z4,z5,z6]),(0,[z0,z2,z3,z4,z394,z5,z6])],[(0,[z108,z0,z2,z23,z4,z5,z6]),(1,[z11,z0,z2,z23,z4,z5]),(0,[z0,z2,z341,z3,z4,z5,z6]),(0,[z0,z395,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z396,z5,z6]),(0,[z0,z2,z3,z78,z4,z5,z90]),(0,[z0,z2,z3,z4,z5,z397,z6])],[(0,[z0,z2,z3,z220,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z141,z6])],[(0,[z0,z2,z3,z4,z398,z5,z6]),(0,[z25,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z399,z5,z6]),(0,[z0,z161,z2,z3,z4,z94,z5]),(0,[z0,z2,z104,z3,z4,z5,z6]),(0,[z400,z0,z2,z3,z4,z5,z6]),(0,[z401,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z88,z3,z4,z5,z90])],[(0,[z0,z2,z3,z402,z4,z5,z6]),(0,[z25,z29,z0,z2,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z180]),(1,[z0,z2,z237,z4,z169,z6]),(0,[z0,z403,z2,z3,z4,z5,z6])],[(1,[z108,z2,z3,z4,z6,z50]),(0,[z0,z2,z3,z4,z5,z404,z6]),(0,[z0,z22,z2,z3,z4,z5,z90]),(0,[z0,z2,z3,z4,z405,z5,z6]),(0,[z198,z403,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z406,z5,z6]),(0,[z0,z2,z3,z44,z4,z5,z90])]],
   [[(1,[z0,z2,z407,z4,z5,z6]),(0,[z133,z2,z8,z3,z4,z5,z6]),(0,[z0,z2,z3,z408,z4,z5,z6]),(0,[z43,z0,z2,z3,z4,z5,z90])],[(0,[z409,z0,z2,z3,z4,z5,z6]),(0,[z170,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z410,z3,z4,z5,z6]),(0,[z0,z2,z3,z411,z4,z5,z6]),(0,[z0,z70,z2,z3,z4,z5,z6])],[(0,[z89,z242,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z9,z4,z5,z6]),(0,[z412,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z69,z6]),(0,[z11,z0,z2,z3,z4,z5,z109]),(0,[z0,z2,z3,z4,z413,z5,z6])],[(0,[z0,z2,z8,z23,z4,z5,z6]),(0,[z43,z0,z2,z9,z4,z5,z6]),(0,[z108,z91,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z414,z6]),(0,[z37,z105,z0,z2,z3,z4,z6]),(0,[z415,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z416,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z417,z6])],[(0,[z0,z2,z3,z4,z5,z6,z418]),(0,[z419,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z93]),(0,[z0,z2,z3,z420,z4,z5,z6]),(0,[z55,z0,z2,z3,z4,z5,z90]),(0,[z0,z2,z3,z4,z421,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z422])],[(0,[z0,z2,z3,z423,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z424]),(0,[z43,z11,z0,z2,z3,z4,z5]),(1,[z37,z11,z0,z2,z3,z4])],[(0,[z0,z2,z23,z99,z4,z5,z6]),(0,[z0,z2,z23,z4,z21,z5,z6]),(0,[z105,z0,z2,z175,z4,z5,z6]),(0,[z0,z2,z3,z425,z4,z5,z6]),(0,[z0,z2,z3,z4,z59,z5,z6])],[(0,[z55,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z426,z23,z4,z5,z6]),(0,[z0,z427,z2,z3,z4,z5,z6]),(0,[z428,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z429,z5,z6]),(0,[z0,z2,z3,z4,z5,z430,z6]),(0,[z431,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z432,z5,z6]),(0,[z0,z2,z3,z4,z5,z433,z6]),(0,[z434,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z256,z4,z5,z6]),(0,[z435,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z184,z90]),(0,[z0,z2,z3,z31,z4,z5,z436])],[(0,[z300,z0,z2,z3,z4,z5,z90]),(0,[z0,z2,z23,z4,z77,z5,z6]),(0,[z0,z2,z437,z23,z4,z5,z6]),(0,[z108,z0,z2,z3,z4,z5,z6]),(0,[z55,z11,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z438,z5,z6]),(0,[z11,z0,z2,z3,z44,z4,z5]),(0,[z0,z2,z3,z4,z439,z5,z90])],[(0,[z0,z2,z3,z4,z440,z5,z6]),(0,[z0,z2,z441,z3,z4,z5,z6])],[(0,[z442,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z9,z4,z188,z5,z6]),(0,[z443,z0,z2,z3,z4,z5,z6]),(1,[z403,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z151,z4,z444,z6]),(0,[z0,z2,z3,z4,z5,z6,z204])],[(0,[z242,z0,z2,z9,z4,z5,z6]),(0,[z300,z0,z2,z9,z4,z5,z6]),(0,[z76,z0,z2,z208,z4,z5,z6]),(0,[z11,z0,z2,z237,z3,z4,z5]),(0,[z0,z2,z445,z3,z4,z5,z6])],[(0,[z0,z446,z2,z3,z4,z5,z6]),(0,[z0,z2,z9,z4,z5,z80,z6]),(0,[z447,z0,z2,z23,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z31,z5,z184,z6])],[(0,[z300,z11,z0,z2,z3,z4,z5]),(0,[z18,z0,z2,z3,z4,z5,z56]),(1,[z0,z2,z3,z4,z5,z436])],[(0,[z0,z2,z448,z3,z4,z5,z6]),(0,[z170,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z77,z5,z184,z6]),(0,[z449,z0,z2,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z5,z6,z56]),(0,[z0,z2,z3,z4,z5,z450,z6]),(1,[z0,z2,z3,z4,z444,z6])]],
   [[(0,[z451,z0,z2,z23,z4,z5,z6]),(1,[z185,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z180]),(0,[z43,z0,z19,z2,z3,z4,z5]),(0,[z452,z0,z2,z3,z4,z5,z6]),(0,[z453,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z454]),(0,[z0,z2,z3,z4,z5,z455,z6]),(0,[z0,z2,z3,z4,z5,z6,z456]),(1,[z0,z2,z3,z113,z4,z5])],[(0,[z37,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z457,z4,z5,z6]),(1,[z0,z2,z458,z3,z4,z5]),(0,[z271,z0,z2,z3,z4,z5,z128]),(1,[z43,z0,z2,z3,z44,z5])],[(0,[z0,z2,z3,z459,z4,z5,z6]),(1,[z108,z2,z9,z4,z5,z6]),(0,[z170,z2,z3,z9,z4,z5,z6]),(0,[z0,z2,z23,z367,z4,z5,z6]),(0,[z92,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z208,z3,z4,z5,z6]),(0,[z108,z2,z3,z4,z5,z6,z50]),(0,[z0,z2,z3,z4,z460,z5,z6]),(0,[z0,z2,z3,z4,z5,z461,z6]),(0,[z18,z0,z2,z3,z151,z4,z5])],[(0,[z0,z2,z3,z462,z4,z5,z6]),(0,[z463,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z464,z4,z5,z6])],[(0,[z0,z2,z426,z3,z4,z5,z6]),(0,[z465,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z378]),(0,[z55,z0,z3,z4,z156,z5,z6]),(0,[z0,z2,z3,z4,z466,z5,z6]),(0,[z0,z2,z3,z99,z4,z5,z424]),(0,[z0,z467,z2,z3,z4,z5,z6])],[(0,[z89,z0,z2,z23,z4,z5,z6]),(0,[z2,z8,z3,z9,z4,z5,z6]),(0,[z468,z0,z2,z3,z4,z5,z6]),(0,[z91,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z469,z23,z4,z5,z6]),(0,[z11,z105,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z470,z4,z5,z6])],[(0,[z0,z2,z3,z471,z4,z5,z6]),(0,[z0,z2,z437,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z472,z6]),(1,[z0,z2,z328,z4,z5,z6]),(1,[z0,z2,z3,z4,z473,z5]),(0,[z0,z2,z3,z4,z474,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z424]),(0,[z0,z2,z3,z475,z4,z5,z6])]],
   [[(0,[z0,z2,z9,z4,z5,z6,z227]),(0,[z11,z0,z2,z23,z4,z5,z6]),(1,[z0,z2,z3,z4,z280,z6]),(0,[z476,z0,z2,z3,z4,z5,z6])],[(0,[z18,z0,z2,z23,z4,z5,z6]),(0,[z105,z2,z3,z4,z49,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z477])],[(0,[z242,z2,z3,z9,z4,z5,z6]),(0,[z300,z2,z3,z9,z4,z5,z6]),(0,[z478,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z156,z90]),(0,[z11,z0,z479,z2,z3,z4,z5])],[(0,[z447,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z480,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z481,z6]),(0,[z0,z482,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z483,z5,z6]),(0,[z11,z0,z133,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z484,z5,z6]),(0,[z0,z285,z2,z3,z4,z5,z6]),(1,[z0,z2,z216,z4,z5,z6]),(0,[z76,z0,z2,z3,z12,z5,z6]),(1,[z0,z34,z35,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z80,z90])],[(0,[z485,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z216,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z486,z6]),(0,[z0,z2,z487,z3,z4,z5,z6]),(0,[z0,z161,z3,z4,z5,z80,z6])],[(0,[z242,z0,z2,z116,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z243]),(0,[z451,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z488,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z94,z5]),(1,[z0,z2,z3,z4,z295,z6])],[(0,[z0,z2,z9,z4,z5,z6,z109]),(0,[z0,z489,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z3,z78,z5,z6]),(0,[z0,z161,z2,z3,z4,z5,z90]),(0,[z490,z0,z2,z3,z4,z5,z6]),(0,[z491,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z9,z4,z156,z5,z6]),(0,[z170,z0,z2,z341,z4,z5,z6]),(0,[z0,z2,z182,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z492,z6]),(0,[z0,z2,z3,z4,z493,z5,z6]),(0,[z0,z2,z3,z4,z5,z494,z6]),(0,[z0,z2,z3,z4,z5,z6,z436]),(0,[z0,z495,z2,z3,z4,z5,z6])],[(1,[z242,z2,z9,z4,z5,z6]),(0,[z297,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z35,z3,z4,z5,z90]),(0,[z92,z0,z2,z3,z4,z5,z6])],[(0,[z0,z161,z2,z9,z4,z5,z6]),(0,[z496,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z497,z5,z6]),(1,[z198,z0,z2,z4,z46,z6]),(0,[z271,z0,z2,z3,z4,z127,z5]),(0,[z209,z0,z2,z3,z4,z5,z90])],[(0,[z498,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z499,z5,z6])],[(0,[z89,z0,z2,z3,z4,z5,z6]),(0,[z91,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z9,z262,z4,z5,z6]),(0,[z0,z2,z35,z9,z4,z5,z6]),(0,[z0,z2,z469,z3,z4,z5,z6]),(0,[z0,z500,z2,z3,z4,z5,z6]),(0,[z501,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z9,z4,z40,z5,z6]),(0,[z0,z2,z23,z4,z5,z69,z6]),(0,[z0,z502,z2,z3,z4,z5,z6])],[(0,[z358,z0,z2,z3,z4,z40,z5]),(0,[z11,z0,z2,z3,z4,z5,z6])],[(0,[z105,z0,z2,z9,z4,z5,z6]),(0,[z108,z105,z2,z3,z4,z5,z6]),(1,[z105,z0,z2,z3,z4,z90]),(0,[z11,z0,z2,z3,z4,z49,z5]),(0,[z68,z0,z2,z3,z4,z5,z90]),(0,[z503,z0,z2,z3,z4,z5,z6]),(0,[z11,z0,z34,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z378]),(1,[z0,z161,z3,z4,z80,z6]),(0,[z18,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z504,z6]),(0,[z505,z0,z2,z3,z4,z5,z90])]],
   [[(0,[z506,z0,z2,z3,z4,z5,z6])],[(0,[z55,z0,z133,z3,z4,z5,z6]),(0,[z0,z2,z23,z4,z59,z5,z6]),(0,[z105,z0,z2,z3,z4,z49,z6]),(0,[z0,z3,z78,z4,z40,z5,z6])],[(0,[z269,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z9,z4,z5,z6,z56]),(0,[z507,z0,z2,z3,z4,z5,z6]),(0,[z108,z0,z2,z3,z4,z6,z90]),(0,[z0,z115,z2,z3,z4,z5,z6])],[(0,[z0,z2,z9,z31,z4,z5,z6]),(0,[z0,z2,z23,z4,z432,z5,z6]),(1,[z146,z2,z3,z4,z5,z109]),(0,[z508,z0,z2,z3,z4,z5,z6]),(0,[z0,z19,z2,z3,z4,z5,z56]),(0,[z0,z2,z73,z4,z21,z5,z6]),(0,[z509,z11,z0,z2,z3,z4,z5])],[(0,[z510,z0,z2,z3,z4,z5,z6]),(0,[z2,z23,z3,z9,z4,z5,z6]),(0,[z68,z11,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z69,z141,z6]),(0,[z0,z2,z511,z3,z4,z5,z6]),(0,[z18,z43,z0,z2,z3,z4,z5]),(0,[z11,z0,z2,z3,z4,z129,z5]),(0,[z0,z2,z512,z3,z4,z5,z6])],[(0,[z0,z2,z9,z151,z4,z5,z6]),(0,[z0,z2,z23,z4,z440,z5,z6]),(0,[z0,z2,z3,z4,z513,z5,z6]),(0,[z514,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z515,z5,z6]),(0,[z18,z0,z2,z3,z4,z129,z5])],[(0,[z0,z2,z3,z4,z5,z516,z6]),(0,[z0,z2,z9,z4,z5,z6,z50]),(0,[z0,z2,z23,z4,z5,z6,z204]),(0,[z146,z0,z2,z517,z4,z5,z6]),(0,[z55,z0,z2,z3,z4,z156,z6])],[(0,[z242,z133,z2,z3,z4,z5,z6]),(0,[z518,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z9,z73,z4,z5,z6]),(0,[z0,z519,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z520,z5,z6]),(0,[z0,z2,z521,z3,z4,z5,z6]),(0,[z0,z2,z3,z522,z4,z5,z6]),(0,[z0,z2,z3,z4,z523,z5,z6]),(0,[z524,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z156,z5,z90]),(0,[z525,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z526,z5,z6]),(0,[z0,z2,z3,z4,z5,z90,z527])]],
   [[(0,[z338,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z517,z3,z4,z5,z6]),(0,[z146,z0,z2,z3,z4,z5,z90]),(0,[z0,z2,z3,z4,z5,z528,z6]),(0,[z529,z0,z2,z3,z4,z5,z6]),(0,[z0,z19,z2,z3,z151,z4,z5])],[(0,[z0,z2,z3,z4,z5,z5,z6])],[(0,[z530,z0,z2,z3,z4,z5,z6]),(0,[z531,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z23,z4,z5,z90])],[(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z92,z0,z2,z3,z31,z4,z6]),(0,[z0,z2,z3,z4,z5,z90,z532])],[(0,[z89,z0,z8,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z533,z5,z6]),(0,[z0,z2,z3,z4,z40,z5,z90]),(0,[z198,z0,z2,z3,z4,z5,z90]),(0,[z11,z0,z2,z3,z4,z534,z5])],[(0,[z0,z2,z317,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z535,z5,z6]),(0,[z146,z11,z0,z2,z3,z4,z5]),(0,[z0,z2,z536,z3,z4,z5,z6]),(0,[z0,z2,z537,z3,z4,z5,z6])],[(0,[z0,z0,z2,z9,z4,z5,z6]),(0,[z0,z19,z2,z23,z4,z5,z6]),(0,[z68,z146,z2,z3,z4,z5,z6]),(0,[z0,z538,z2,z3,z4,z5,z6]),(0,[z539,z0,z2,z3,z4,z5,z6])],[(1,[z300,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z5,z90]),(0,[z0,z2,z3,z4,z5,z6,z540]),(0,[z0,z2,z3,z4,z541,z5,z6]),(0,[z0,z2,z3,z542,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z543,z6])]],
   [[(0,[z544,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z545,z3,z4,z5,z6]),(0,[z546,z0,z2,z3,z4,z5,z6])],[(0,[z68,z0,z2,z547,z4,z5,z6]),(0,[z37,z0,z2,z3,z4,z156,z6]),(0,[z198,z11,z0,z2,z3,z4,z5])],[(0,[z548,z0,z2,z3,z4,z5,z6]),(0,[z108,z0,z2,z3,z4,z5,z93]),(0,[z549,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z550,z3,z4,z5,z6]),(0,[z271,z0,z2,z3,z4,z5,z6]),(0,[z551,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z552,z3,z4,z5,z6]),(0,[z0,z2,z3,z31,z4,z5,z90])],[(0,[z47,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z553,z4,z5,z6]),(0,[z29,z0,z2,z104,z4,z5,z6]),(1,[z0,z2,z165,z4,z5,z128]),(0,[z0,z2,z3,z44,z151,z4,z5]),(0,[z0,z2,z3,z4,z5,z90,z90])],[(0,[z554,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z555,z4,z5,z6]),(0,[z0,z2,z3,z151,z4,z5,z90])],[(0,[z556,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z557,z5,z6]),(0,[z269,z0,z3,z4,z40,z5,z6]),(0,[z0,z2,z558,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z129,z5,z6]),(1,[z0,z2,z3,z150,z4,z6])],[(0,[z242,z0,z2,z220,z4,z5,z6]),(0,[z0,z2,z3,z391,z4,z5,z6]),(1,[z0,z217,z3,z4,z5,z6]),(1,[z0,z2,z517,z4,z5,z6]),(1,[z358,z0,z2,z3,z4,z5]),(0,[z559,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z73,z4,z5,z90])],[(0,[z0,z2,z9,z26,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z560]),(0,[z0,z2,z3,z4,z561,z5,z6])]],
   [[(0,[z0,z2,z3,z562,z4,z5,z6]),(0,[z563,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z90])],[(0,[z0,z2,z9,z99,z4,z5,z6]),(0,[z0,z564,z2,z3,z4,z5,z6]),(0,[z68,z0,z2,z328,z4,z5,z6]),(0,[z0,z2,z237,z4,z5,z169,z6]),(1,[z92,z0,z2,z3,z31,z6])],[(0,[z565,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z339,z5,z6]),(0,[z43,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z566]),(0,[z0,z2,z3,z567,z4,z5,z6]),(0,[z0,z2,z165,z3,z4,z5,z6]),(0,[z0,z2,z3,z568,z4,z5,z6])],[(1,[z242,z133,z3,z4,z5,z6]),(1,[z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z569,z4,z5,z6]),(0,[z0,z2,z3,z570,z4,z5,z6]),(0,[z571,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z458,z3,z4,z5,z6]),(0,[z0,z2,z3,z150,z4,z5,z6])],[(0,[z0,z2,z9,z4,z77,z5,z6]),(0,[z91,z2,z3,z4,z77,z5,z6]),(0,[z68,z0,z2,z3,z4,z5,z69]),(0,[z0,z19,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z572,z5,z6]),(0,[z0,z2,z3,z4,z573,z5,z6])],[(0,[z0,z2,z3,z4,z473,z5,z6]),(0,[z574,z0,z2,z3,z4,z5,z6]),(1,[z11,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z381,z4,z5,z6])],[(0,[z0,z2,z3,z575,z4,z5,z6]),(0,[z0,z34,z2,z3,z4,z5,z90]),(0,[z0,z2,z576,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z577,z6]),(0,[z0,z2,z3,z4,z5,z6,z578]),(0,[z0,z2,z3,z4,z5,z6,z527]),(0,[z0,z479,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z246,z5,z6]),(0,[z269,z0,z2,z3,z78,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z579]),(0,[z11,z0,z2,z3,z4,z6,z90])]],
   [[(0,[z0,z2,z3,z580,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z581,z6]),(0,[z0,z2,z3,z4,z534,z5,z6])],[(0,[z0,z582,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z583,z6]),(0,[z0,z161,z2,z3,z4,z156,z6]),(0,[z0,z2,z3,z4,z584,z5,z6])],[(0,[z0,z133,z3,z4,z5,z80,z6]),(0,[z0,z2,z3,z4,z5,z6,z532]),(0,[z0,z19,z2,z3,z4,z129,z5]),(0,[z0,z2,z3,z4,z5,z169,z6])],[(0,[z242,z0,z2,z23,z4,z5,z6]),(0,[z300,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z23,z4,z49,z5,z6]),(0,[z105,z0,z2,z177,z4,z5,z6]),(0,[z0,z2,z3,z4,z39,z5,z6]),(0,[z0,z2,z3,z4,z585,z5,z6]),(0,[z586,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z295,z5,z6]),(0,[z0,z2,z3,z4,z587,z5,z6])],[(0,[z0,z133,z2,z3,z4,z5,z90]),(0,[z11,z0,z2,z3,z4,z156,z5]),(0,[z0,z2,z3,z588,z4,z5,z6]),(0,[z43,z0,z2,z3,z151,z5,z6]),(0,[z11,z0,z2,z3,z4,z5,z204])],[(0,[z589,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z323,z9,z4,z5,z6]),(0,[z0,z2,z590,z23,z4,z5,z6]),(0,[z146,z0,z2,z3,z4,z5,z69]),(0,[z29,z0,z2,z3,z21,z5,z6]),(0,[z29,z0,z2,z3,z4,z5,z90]),(0,[z0,z2,z3,z4,z140,z5,z90])],[(0,[z591,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z12,z5,z184,z6]),(0,[z0,z2,z3,z4,z5,z592,z6]),(0,[z0,z2,z3,z26,z4,z5,z90])],[(0,[z0,z133,z2,z9,z4,z5,z6]),(0,[z412,z0,z2,z3,z4,z5,z6]),(0,[z593,z0,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z594,z5,z6]),(1,[z0,z2,z3,z4,z5,z595]),(0,[z0,z2,z3,z4,z596,z5,z6]),(0,[z0,z2,z3,z44,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z597,z6])]],
   [[(0,[z29,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z598,z5,z6]),(0,[z271,z0,z2,z165,z4,z5,z6]),(0,[z43,z0,z2,z3,z4,z5,z6])],[(0,[z89,z0,z2,z407,z4,z5,z6]),(1,[z2,z9,z4,z77,z5,z6]),(0,[z37,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z599,z3,z4,z5,z6]),(0,[z600,z0,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z99,z4,z5])],[(1,[z0,z2,z547,z4,z5,z6]),(1,[z0,z2,z3,z4,z39,z5]),(0,[z29,z11,z0,z2,z3,z4,z5]),(0,[z0,z2,z237,z3,z4,z473,z5]),(0,[z0,z2,z3,z601,z4,z5,z6]),(1,[z0,z2,z3,z31,z4,z90]),(0,[z602,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z90]),(0,[z0,z2,z84,z3,z4,z5,z6])],[(0,[z0,z2,z407,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z77,z5,z90]),(0,[z0,z2,z3,z547,z4,z5,z6])],[(0,[z603,z0,z2,z3,z4,z5,z6]),(0,[z0,z604,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z605,z6]),(0,[z0,z2,z3,z4,z606,z5,z6]),(0,[z607,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z608,z3,z4,z5,z6])],[(0,[z609,z0,z2,z3,z4,z5,z6]),(0,[z91,z2,z23,z3,z4,z5,z6]),(0,[z0,z610,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z104,z3,z4,z5]),(0,[z0,z2,z3,z4,z611,z5,z6])],[(0,[z612,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z9,z4,z127,z5,z6]),(0,[z0,z2,z3,z4,z5,z613,z6]),(0,[z614,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z9,z4,z5,z184,z6]),(0,[z170,z2,z3,z12,z4,z5,z6]),(1,[z0,z2,z4,z131,z5,z6]),(0,[z29,z0,z2,z3,z73,z5,z6]),(1,[z0,z2,z3,z4,z59,z90])]],
   [[(0,[z0,z2,z3,z615,z4,z5,z6]),(1,[z55,z0,z3,z4,z156,z6])],[(0,[z242,z0,z2,z3,z4,z5,z6]),(0,[z300,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z616]),(0,[z617,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z618,z4,z5,z6]),(0,[z619,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z439,z5,z6])],[(0,[z620,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z621,z6]),(0,[z0,z2,z3,z622,z4,z5,z6]),(0,[z623,z0,z2,z3,z4,z5,z6])],[(0,[z624,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z590,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z625,z5,z6]),(0,[z0,z2,z3,z4,z626,z5,z6])],[(0,[z0,z8,z3,z4,z5,z80,z6]),(0,[z0,z231,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z377]),(0,[z0,z2,z3,z4,z627,z5,z6]),(0,[z0,z2,z3,z4,z5,z628,z6]),(0,[z0,z2,z3,z629,z4,z5,z6])],[(0,[z0,z2,z3,z4,z630,z5,z6]),(0,[z0,z2,z631,z3,z4,z5,z6]),(0,[z0,z2,z9,z4,z46,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z632]),(0,[z0,z2,z3,z4,z5,z633,z6])],[(1,[z0,z2,z194,z4,z5,z6]),(0,[z634,z0,z2,z3,z4,z5,z6]),(0,[z91,z170,z2,z3,z4,z5,z6]),(0,[z271,z0,z2,z4,z127,z5,z6])],[(0,[z0,z2,z3,z194,z4,z5,z6]),(0,[z635,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z636,z5,z6]),(0,[z0,z2,z3,z4,z637,z5,z6]),(0,[z37,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z9,z4,z5,z69,z6]),(0,[z76,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z23,z4,z129,z5,z6]),(0,[z0,z2,z23,z4,z557,z5,z6]),(0,[z638,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z639,z6])],[(0,[z0,z2,z3,z4,z5,z6,z640]),(0,[z11,z0,z2,z3,z4,z40,z5]),(0,[z0,z2,z3,z4,z5,z641,z6]),(0,[z0,z2,z3,z4,z5,z6,z595]),(0,[z0,z2,z3,z4,z5,z205,z90])],[(0,[z0,z2,z3,z4,z642,z5,z6]),(0,[z368,z11,z0,z2,z3,z4,z5])],[(0,[z0,z2,z3,z38,z4,z5,z6]),(0,[z0,z2,z643,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z644,z5,z6]),(0,[z0,z2,z3,z4,z5,z90,z128])],[(0,[z0,z2,z3,z4,z80,z6,z90]),(0,[z0,z2,z3,z645,z4,z5,z6]),(0,[z0,z2,z3,z4,z646,z5,z6]),(0,[z0,z2,z3,z4,z647,z5,z6]),(0,[z0,z2,z3,z151,z5,z6,z204])],[(0,[z0,z2,z23,z4,z5,z6,z566]),(1,[z0,z2,z175,z4,z5,z6]),(0,[z296,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z648,z5,z6]),(0,[z0,z2,z3,z4,z649,z5,z6]),(0,[z0,z2,z3,z4,z127,z5,z90]),(0,[z0,z2,z650,z3,z4,z5,z6])],[(0,[z105,z0,z2,z23,z4,z5,z6]),(0,[z651,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z652,z3,z4,z5,z6]),(0,[z0,z2,z653,z3,z4,z5,z6]),(0,[z0,z2,z3,z99,z5,z184,z6]),(0,[z0,z2,z3,z4,z5,z184,z90]),(0,[z0,z2,z3,z4,z5,z654,z6]),(1,[z11,z0,z2,z3,z4,z90]),(0,[z379,z11,z0,z2,z3,z4,z5])],[(0,[z314,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z655]),(0,[z656,z0,z2,z3,z4,z5,z6]),(0,[z174,z0,z2,z3,z4,z5,z90])]],
   [[(0,[z0,z657,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z658,z4,z5,z6]),(0,[z0,z2,z3,z659,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z660,z6]),(0,[z0,z2,z3,z99,z4,z184,z6])],[(0,[z242,z0,z8,z3,z4,z5,z6]),(0,[z0,z2,z9,z4,z5,z6,z204]),(0,[z661,z0,z2,z3,z4,z5,z6]),(0,[z269,z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z458,z3,z4,z156,z5]),(0,[z662,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z663,z4,z5,z6])],[(0,[z174,z0,z2,z9,z4,z5,z6]),(0,[z25,z0,z2,z3,z4,z5,z90]),(0,[z0,z2,z3,z4,z664,z5,z6]),(0,[z0,z2,z3,z4,z59,z6,z90])],[(0,[z0,z2,z3,z4,z49,z5,z6]),(0,[z269,z0,z22,z3,z4,z5,z6]),(0,[z0,z2,z665,z3,z4,z5,z6])],[(0,[z0,z2,z9,z12,z4,z5,z6]),(0,[z0,z2,z217,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z666,z5,z6]),(0,[z0,z2,z3,z4,z5,z80,z6]),(0,[z0,z2,z3,z4,z46,z5,z90]),(0,[z174,z11,z0,z2,z3,z4,z5])],[(0,[z68,z0,z2,z9,z4,z5,z6]),(0,[z25,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z23,z4,z5,z169,z6]),(0,[z0,z2,z3,z667,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z444,z6])],[(0,[z76,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z668,z4,z5,z6]),(0,[z669,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z377]),(0,[z0,z2,z3,z670,z4,z5,z6])],[(0,[z89,z2,z8,z3,z4,z5,z6]),(0,[z91,z2,z8,z3,z4,z5,z6]),(0,[z271,z0,z2,z23,z4,z5,z6]),(0,[z25,z11,z0,z2,z3,z4,z5]),(0,[z0,z161,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z671,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z672,z6])],[(0,[z0,z2,z35,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z673,z5,z6]),(0,[z37,z0,z2,z3,z31,z4,z6])],[(0,[z11,z0,z2,z3,z9,z4,z5]),(0,[z0,z2,z674,z3,z4,z5,z6]),(0,[z675,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z23,z44,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z90,z56]),(0,[z11,z0,z2,z3,z4,z5,z5])],[(0,[z0,z676,z2,z3,z4,z5,z6]),(0,[z0,z2,z677,z3,z4,z5,z6]),(0,[z0,z678,z2,z3,z4,z5,z6])],[(0,[z2,z3,z9,z4,z49,z5,z6]),(0,[z0,z2,z3,z4,z679,z5,z6]),(0,[z680,z0,z2,z3,z4,z5,z6]),(0,[z105,z0,z2,z3,z4,z5,z6]),(0,[z338,z0,z2,z3,z4,z49,z5])],[(0,[z0,z2,z23,z4,z5,z6,z90]),(0,[z681,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z682,z6]),(0,[z146,z0,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z90,z50]),(0,[z509,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z683,z4,z5,z6]),(0,[z684,z0,z2,z3,z4,z5,z6]),(0,[z685,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z280,z6]),(0,[z43,z0,z2,z3,z4,z5,z204]),(0,[z43,z0,z2,z3,z44,z4,z5]),(0,[z37,z0,z2,z3,z4,z59,z6])],[(0,[z686,z0,z2,z3,z4,z5,z6]),(0,[z0,z255,z2,z9,z4,z5,z6]),(0,[z687,z0,z2,z3,z4,z5,z6]),(0,[z269,z0,z2,z3,z4,z5,z6]),(0,[z505,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z116,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z688]),(0,[z0,z2,z3,z31,z4,z573,z5]),(0,[z272,z0,z2,z3,z4,z5,z90])],[(0,[z170,z0,z2,z391,z4,z5,z6]),(0,[z689,z0,z2,z3,z4,z5,z6]),(0,[z431,z11,z0,z2,z3,z4,z5]),(0,[z428,z11,z0,z2,z3,z4,z5])],[(0,[z198,z0,z2,z9,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z77,z5]),(0,[z0,z2,z3,z4,z690,z5,z6]),(0,[z691,z0,z2,z3,z4,z5,z6]),(1,[z63,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z128]),(0,[z0,z2,z3,z4,z5,z692,z6]),(0,[z0,z2,z3,z693,z4,z5,z6])],[(0,[z0,z2,z3,z4,z694,z5,z6]),(0,[z0,z2,z3,z12,z4,z5,z90]),(0,[z108,z11,z0,z2,z3,z4,z5]),(0,[z0,z2,z237,z3,z4,z5,z90]),(0,[z0,z2,z3,z4,z46,z5,z595])],[(0,[z0,z2,z3,z4,z695,z5,z6]),(0,[z11,z0,z2,z3,z26,z4,z5]),(0,[z696,z0,z2,z3,z4,z5,z6]),(0,[z697,z0,z2,z3,z4,z5,z6])],[(1,[z170,z2,z9,z4,z5,z6]),(0,[z66,z0,z2,z23,z4,z5,z6]),(0,[z185,z0,z2,z3,z4,z69,z6]),(0,[z0,z698,z2,z3,z4,z5,z6]),(0,[z0,z2,z699,z3,z4,z5,z6])],[(0,[z0,z2,z8,z3,z4,z5,z90]),(0,[z0,z2,z237,z9,z4,z5,z6]),(0,[z0,z2,z700,z3,z4,z5,z6]),(0,[z11,z0,z22,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z701,z5,z6]),(1,[z0,z2,z3,z4,z573,z5]),(0,[z702,z0,z2,z3,z4,z5,z6])],[(0,[z170,z0,z2,z3,z77,z5,z6]),(0,[z0,z2,z3,z4,z703,z5,z6]),(0,[z0,z2,z3,z4,z156,z5,z6]),(0,[z0,z2,z3,z704,z4,z5,z6]),(0,[z0,z2,z3,z705,z4,z5,z6]),(0,[z0,z706,z2,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z2,z182,z13,z5,z6]),(0,[z18,z0,z3,z4,z707,z5]),(0,[z0,z2,z4,z708,z5,z6])],[(0,[z0,z308,z35,z4,z5,z6]),(0,[z0,z2,z709,z4,z5,z6]),(0,[z2,z3,z4,z5,z710,z6]),(0,[z0,z711,z3,z4,z5,z6]),(0,[z0,z2,z712,z4,z5,z90])],[(0,[z0,z2,z3,z4,z713,z6]),(0,[z0,z2,z714,z4,z5,z6]),(0,[z0,z2,z23,z4,z715,z6]),(0,[z63,z198,z2,z4,z46,z6]),(0,[z509,z70,z2,z3,z4,z5])],[(0,[z2,z9,z4,z369,z5,z6]),(0,[z105,z0,z2,z9,z4,z90]),(0,[z524,z2,z9,z4,z5,z6]),(0,[z11,z0,z2,z341,z4,z5]),(0,[z0,z2,z3,z4,z5,z716]),(0,[z0,z231,z3,z4,z5,z218]),(0,[z269,z0,z3,z40,z5,z90]),(0,[z0,z2,z3,z381,z184,z90]),(0,[z11,z717,z2,z3,z4,z5])],[(0,[z0,z2,z718,z4,z5,z6]),(0,[z25,z17,z26,z4,z5,z6]),(0,[z0,z226,z2,z3,z4,z90])],[(0,[z142,z2,z9,z4,z5,z6]),(0,[z297,z0,z2,z4,z127,z5]),(0,[z2,z3,z4,z719,z5,z6]),(0,[z0,z2,z720,z4,z5,z6]),(0,[z0,z2,z721,z4,z5,z6]),(0,[z0,z2,z3,z722,z5,z90])],[(0,[z0,z2,z3,z4,z723,z6]),(0,[z2,z9,z4,z49,z5,z377]),(0,[z0,z2,z9,z4,z724,z5]),(0,[z0,z217,z3,z4,z6,z90]),(0,[z0,z2,z202,z13,z5,z6]),(0,[z146,z2,z256,z4,z5,z109]),(0,[z185,z11,z0,z2,z3,z4])],[(0,[z0,z2,z725,z4,z5,z6]),(0,[z0,z2,z726,z4,z5,z6]),(0,[z0,z3,z4,z727,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z728,z5]),(0,[z0,z2,z3,z4,z5,z729]),(0,[z0,z730,z3,z4,z5,z6]),(0,[z0,z2,z3,z580,z4,z90]),(0,[z0,z2,z88,z4,z5,z336])],[(0,[z2,z731,z3,z4,z5,z6]),(0,[z2,z347,z9,z4,z5,z6]),(0,[z18,z0,z9,z4,z129,z5]),(0,[z76,z2,z3,z719,z5,z6]),(0,[z0,z732,z3,z4,z5,z6]),(0,[z733,z2,z3,z4,z5,z90])],[(0,[z89,z8,z9,z4,z5,z6]),(0,[z0,z2,z3,z734,z5,z6]),(0,[z2,z9,z4,z386,z5,z6]),(0,[z37,z11,z0,z2,z23,z4]),(0,[z105,z2,z3,z4,z49,z6]),(0,[z0,z2,z3,z4,z605,z90]),(0,[z0,z3,z4,z735,z5,z6]),(0,[z0,z2,z736,z4,z5,z6])],[(0,[z737,z0,z2,z3,z4,z5])],[(0,[z0,z2,z9,z151,z5,z204]),(0,[z0,z2,z3,z13,z5,z218]),(0,[z142,z2,z73,z4,z5,z6]),(0,[z0,z2,z738,z4,z5,z6]),(0,[z145,z0,z344,z3,z4,z5])],[(0,[z2,z8,z194,z4,z5,z6]),(0,[z2,z9,z4,z5,z397,z6]),(0,[z0,z3,z4,z156,z735,z6]),(0,[z11,z0,z2,z3,z4,z90])],[(0,[z325,z0,z2,z3,z4,z90]),(0,[z0,z2,z3,z4,z5,z739]),(0,[z76,z2,z9,z77,z5,z6]),(0,[z412,z2,z9,z77,z5,z6]),(0,[z0,z2,z391,z4,z5,z90]),(0,[z0,z740,z3,z4,z5,z6]),(0,[z0,z2,z237,z4,z473,z169])],[(0,[z0,z2,z182,z4,z5,z6]),(0,[z0,z2,z3,z4,z741,z6]),(0,[z0,z2,z3,z246,z6,z90]),(0,[z68,z2,z3,z4,z5,z742]),(0,[z0,z2,z743,z4,z5,z6]),(0,[z0,z82,z2,z3,z4,z90])]],
   [[(0,[z0,z2,z744,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z745]),(0,[z0,z2,z3,z4,z715,z6]),(0,[z0,z231,z3,z13,z5,z6]),(0,[z0,z479,z3,z4,z129,z5])],[(0,[z170,z2,z23,z12,z5,z6]),(0,[z0,z231,z23,z4,z5,z6]),(0,[z563,z2,z23,z4,z5,z6]),(0,[z108,z217,z3,z4,z6,z50]),(0,[z11,z0,z2,z3,z246,z5]),(0,[z0,z2,z3,z4,z5,z746]),(0,[z0,z2,z747,z4,z5,z6])],[(1,[z748,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z628,z90]),(0,[z0,z2,z237,z4,z169,z90])],[(0,[z366,z2,z9,z4,z5,z6]),(0,[z63,z2,z23,z4,z5,z6]),(0,[z0,z2,z749,z4,z5,z6]),(0,[z43,z0,z2,z3,z4,z280])],[(0,[z0,z2,z407,z4,z5,z90]),(0,[z2,z748,z3,z4,z5,z6]),(0,[z92,z2,z9,z77,z5,z6]),(0,[z297,z0,z2,z4,z103,z5]),(0,[z0,z2,z23,z4,z80,z90]),(0,[z53,z2,z23,z4,z5,z6])],[(0,[z531,z2,z9,z4,z5,z6]),(0,[z11,z2,z23,z9,z4,z5]),(0,[z0,z2,z9,z4,z5,z180]),(0,[z0,z2,z590,z4,z5,z566]),(0,[z0,z2,z3,z151,z594,z5])],[(0,[z108,z2,z9,z4,z6,z50]),(0,[z2,z9,z4,z421,z5,z6]),(0,[z697,z2,z9,z4,z5,z6]),(0,[z0,z2,z317,z4,z5,z128]),(0,[z0,z217,z3,z4,z5,z93]),(0,[z108,z0,z2,z3,z4,z377]),(0,[z0,z2,z3,z4,z750,z6]),(0,[z0,z2,z3,z4,z751,z5]),(0,[z0,z2,z3,z4,z752,z6]),(0,[z753,z2,z3,z4,z5,z6]),(0,[z0,z2,z344,z3,z4,z90])],[(0,[z2,z9,z423,z4,z5,z6]),(0,[z91,z11,z2,z23,z4,z5]),(0,[z0,z2,z23,z4,z573,z5]),(0,[z108,z0,z2,z3,z13,z90]),(0,[z0,z2,z754,z4,z5,z6]),(0,[z272,z2,z3,z4,z5,z109]),(0,[z755,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z208,z4,z5,z6]),(0,[z0,z2,z756,z4,z5,z6]),(0,[z105,z2,z3,z4,z205,z6]),(0,[z271,z0,z2,z4,z757,z5]),(0,[z758,z0,z2,z3,z4,z5]),(0,[z11,z0,z2,z759,z4,z5])],[(0,[z170,z11,z2,z9,z4,z5]),(0,[z0,z2,z9,z4,z5,z760]),(0,[z0,z2,z3,z4,z5,z761]),(0,[z0,z2,z762,z4,z5,z90])],[(0,[z2,z9,z4,z432,z5,z6]),(0,[z763,z0,z9,z4,z5,z6]),(0,[z0,z764,z2,z9,z4,z6]),(0,[z0,z2,z23,z13,z5,z6]),(0,[z0,z2,z23,z4,z5,z238]),(0,[z0,z2,z3,z12,z184,z90]),(0,[z108,z2,z3,z246,z6,z50]),(0,[z29,z142,z2,z4,z5,z6]),(0,[z0,z2,z3,z765,z4,z5]),(0,[z0,z2,z766,z4,z5,z6])],[(0,[z767,z0,z2,z3,z4,z5]),(0,[z2,z23,z9,z4,z5,z6]),(0,[z0,z2,z9,z4,z5,z93]),(0,[z0,z2,z3,z4,z5,z768]),(0,[z0,z2,z3,z4,z5,z218]),(0,[z0,z2,z256,z4,z5,z90]),(0,[z0,z2,z3,z4,z5,z769]),(0,[z0,z2,z3,z4,z5,z770]),(0,[z0,z2,z771,z4,z5,z6])],[(0,[z0,z748,z3,z4,z5,z6]),(0,[z0,z285,z2,z4,z339,z6]),(0,[z0,z2,z9,z4,z5,z424]),(0,[z17,z2,z23,z4,z5,z6]),(0,[z2,z3,z4,z5,z69,z742]),(0,[z142,z2,z26,z4,z5,z6]),(0,[z269,z130,z0,z40,z5,z6])],[(0,[z92,z0,z2,z9,z31,z6]),(0,[z0,z2,z3,z772,z5,z6]),(0,[z108,z91,z2,z3,z4,z90]),(0,[z11,z0,z2,z3,z4,z24]),(0,[z0,z2,z773,z4,z5,z6]),(0,[z0,z2,z3,z4,z774,z6]),(0,[z0,z2,z3,z31,z184,z90]),(0,[z0,z2,z3,z4,z775,z90])],[(0,[z0,z2,z776,z4,z5,z6]),(0,[z393,z2,z9,z4,z5,z6]),(0,[z271,z0,z2,z4,z440,z5]),(0,[z0,z777,z26,z4,z5,z6]),(0,[z0,z2,z3,z4,z660,z90]),(0,[z0,z2,z3,z778,z4,z5])],[(0,[z0,z231,z3,z4,z5,z6]),(0,[z779,z0,z2,z9,z5,z6]),(0,[z0,z2,z9,z4,z184,z90]),(0,[z2,z341,z9,z4,z5,z6]),(0,[z170,z2,z3,z12,z5,z6]),(0,[z0,z2,z3,z246,z5,z93]),(0,[z780,z2,z3,z4,z5,z6]),(0,[z403,z2,z3,z4,z5,z90]),(0,[z0,z2,z781,z4,z5,z6])]],
   [[(0,[z11,z242,z133,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z782]),(0,[z0,z2,z783,z4,z5,z6])],[(0,[z63,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z9,z4,z5]),(0,[z2,z9,z77,z5,z184,z6]),(0,[z0,z2,z784,z4,z5,z6]),(0,[z785,z0,z2,z4,z5,z6]),(0,[z18,z0,z132,z3,z4,z5]),(0,[z0,z2,z786,z4,z5,z90])],[(0,[z53,z2,z3,z4,z5,z6]),(0,[z403,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z80,z90])],[(1,[z108,z2,z9,z4,z90]),(0,[z0,z2,z9,z4,z787,z6]),(0,[z788,z0,z2,z9,z4,z5]),(0,[z0,z2,z789,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z790]),(0,[z0,z2,z3,z4,z429,z90]),(0,[z0,z2,z3,z4,z444,z90]),(0,[z92,z0,z2,z3,z31,z436])],[(0,[z170,z2,z9,z4,z5,z6]),(0,[z108,z191,z2,z3,z4,z6]),(0,[z105,z2,z177,z4,z49,z6]),(0,[z185,z0,z2,z3,z4,z90]),(0,[z717,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z757,z5,z128])],[(0,[z108,z217,z9,z4,z5,z6]),(0,[z0,z2,z9,z4,z5,z436]),(0,[z68,z2,z23,z4,z5,z69]),(0,[z0,z2,z791,z4,z5,z6]),(0,[z0,z2,z3,z4,z573,z5]),(0,[z2,z3,z4,z5,z792,z6]),(0,[z0,z2,z793,z4,z5,z90])],[(0,[z0,z2,z794,z9,z4,z5]),(0,[z0,z2,z9,z4,z444,z6])],[(0,[z0,z2,z3,z4,z795,z6]),(0,[z108,z2,z9,z4,z5,z90]),(0,[z284,z2,z9,z4,z5,z6]),(0,[z29,z53,z2,z21,z5,z6])]],
   [[(0,[z242,z173,z3,z4,z5,z6]),(0,[z338,z2,z9,z4,z49,z5]),(0,[z0,z2,z9,z4,z5,z796]),(0,[z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z238])],[(0,[z0,z2,z23,z4,z5,z6]),(0,[z2,z9,z4,z5,z472,z6]),(0,[z0,z2,z797,z9,z4,z6]),(0,[z0,z2,z9,z203,z4,z5]),(0,[z0,z2,z3,z4,z798,z6]),(0,[z271,z0,z2,z4,z140,z5]),(0,[z0,z2,z3,z31,z4,z775])],[(0,[z17,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z799,z4,z6]),(0,[z529,z2,z9,z4,z5,z6]),(0,[z185,z0,z2,z23,z4,z6]),(0,[z0,z2,z3,z4,z800,z6]),(0,[z0,z801,z3,z4,z5,z6]),(0,[z802,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z203,z99,z184])],[(0,[z0,z2,z3,z803,z5,z6]),(0,[z0,z2,z3,z4,z5,z804]),(0,[z0,z2,z328,z4,z5,z90]),(0,[z509,z0,z2,z3,z4,z141]),(0,[z0,z2,z3,z805,z4,z6])],[(0,[z0,z2,z3,z806,z5,z6]),(0,[z0,z2,z9,z4,z5,z378]),(0,[z0,z2,z458,z23,z4,z5]),(0,[z0,z2,z23,z99,z184,z6]),(0,[z43,z0,z2,z23,z44,z5]),(0,[z0,z2,z3,z4,z280,z90]),(0,[z0,z2,z807,z4,z5,z6])],[(0,[z117,z0,z2,z557,z5,z6]),(0,[z0,z2,z3,z4,z5,z808]),(0,[z0,z2,z3,z4,z584,z90]),(0,[z809,z2,z3,z4,z5,z6])],[(0,[z2,z9,z4,z483,z5,z6]),(0,[z0,z2,z4,z810,z5,z6]),(0,[z2,z9,z4,z484,z5,z6]),(0,[z108,z2,z9,z246,z5,z6]),(0,[z0,z2,z9,z4,z473,z5]),(0,[z0,z811,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z812]),(0,[z0,z2,z3,z4,z363,z90])],[(0,[z0,z2,z813,z4,z5,z6]),(0,[z241,z0,z2,z3,z4,z90]),(0,[z2,z3,z4,z5,z742,z6]),(0,[z0,z2,z814,z4,z5,z6]),(0,[z815,z11,z2,z3,z4,z5])]],
   [[(0,[z0,z22,z23,z78,z5,z6]),(0,[z66,z0,z2,z4,z432,z6]),(0,[z0,z2,z216,z4,z5,z90]),(0,[z170,z2,z341,z12,z5,z6]),(0,[z0,z34,z35,z4,z5,z90]),(0,[z0,z2,z3,z4,z39,z816]),(0,[z586,z0,z2,z3,z4,z90]),(0,[z11,z0,z2,z3,z4,z361]),(0,[z0,z2,z3,z4,z692,z90])],[(0,[z0,z2,z817,z4,z5,z6]),(0,[z0,z2,z9,z4,z156,z90]),(0,[z400,z2,z9,z4,z5,z6]),(0,[z25,z0,z777,z4,z5,z6]),(0,[z0,z2,z3,z4,z184,z424]),(0,[z11,z0,z2,z3,z4,z444])],[(0,[z0,z8,z3,z4,z80,z90]),(0,[z0,z2,z3,z4,z295,z90]),(0,[z0,z2,z3,z20,z184,z90]),(0,[z818,z2,z3,z4,z5,z90])],[(0,[z0,z2,z104,z367,z5,z6]),(0,[z53,z2,z341,z4,z5,z6]),(0,[z68,z2,z3,z4,z5,z69]),(0,[z130,z819,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z497,z90])],[(0,[z0,z2,z3,z820,z5,z6]),(0,[z209,z2,z3,z4,z5,z205])],[(0,[z2,z8,z9,z4,z5,z6]),(0,[z242,z2,z9,z4,z5,z90]),(0,[z0,z2,z3,z4,z5,z821]),(0,[z0,z2,z822,z4,z5,z6]),(0,[z0,z2,z823,z4,z5,z6]),(0,[z25,z0,z26,z4,z5,z90]),(0,[z0,z2,z3,z4,z824,z5]),(0,[z0,z2,z825,z4,z5,z6]),(0,[z0,z2,z826,z4,z5,z6])],[(0,[z0,z2,z9,z4,z827,z5]),(0,[z0,z2,z182,z4,z5,z218]),(0,[z0,z2,z3,z4,z7,z90]),(0,[z198,z0,z2,z4,z46,z90])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z55,z8,z9,z4,z5,z6]),(0,[z147,z2,z9,z4,z5,z6]),(0,[z265,z2,z3,z4,z5,z6]),(0,[z0,z2,z23,z4,z141,z6]),(0,[z67,z0,z2,z84,z4,z5])]],
   [[(0,[z0,z676,z2,z3,z4,z90]),(0,[z349,z2,z23,z4,z5,z6]),(0,[z828,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z39,z131,z5]),(0,[z0,z2,z829,z4,z5,z6])],[(0,[z463,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z830,z90]),(0,[z0,z2,z3,z4,z541,z90])],[(0,[z2,z9,z4,z49,z5,z6]),(0,[z0,z2,z3,z668,z4,z90]),(0,[z55,z0,z3,z4,z735,z6]),(0,[z0,z2,z3,z99,z184,z6]),(0,[z0,z2,z3,z4,z30,z90])],[(0,[z0,z2,z3,z4,z32,z90]),(0,[z2,z437,z9,z4,z5,z6]),(0,[z0,z489,z2,z3,z4,z90]),(0,[z0,z2,z3,z831,z5,z6]),(0,[z0,z2,z3,z4,z832,z5])],[(0,[z76,z2,z208,z77,z5,z6]),(0,[z0,z2,z202,z4,z5,z218]),(0,[z0,z19,z2,z3,z4,z444]),(0,[z0,z2,z3,z4,z5,z833])],[(0,[z230,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z834,z6]),(0,[z447,z0,z38,z4,z5,z6]),(0,[z146,z2,z517,z4,z5,z109]),(0,[z0,z2,z3,z4,z835,z6]),(1,[z758,z0,z2,z3,z4])],[(0,[z0,z2,z836,z4,z5,z6]),(0,[z0,z22,z3,z78,z5,z6]),(0,[z0,z2,z3,z4,z5,z837]),(0,[z0,z115,z3,z4,z80,z6])],[(0,[z0,z2,z3,z4,z838,z6]),(0,[z2,z9,z4,z513,z5,z6]),(0,[z839,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z311,z9,z4,z5,z6]),(0,[z0,z231,z202,z4,z5,z6]),(0,[z0,z2,z182,z4,z5,z93]),(0,[z68,z2,z3,z4,z69,z141]),(0,[z840,z0,z2,z3,z5,z6]),(0,[z0,z3,z4,z707,z5,z6])],[(0,[z0,z2,z3,z4,z5,z841]),(0,[z105,z0,z2,z23,z4,z90]),(0,[z0,z2,z842,z4,z5,z6]),(0,[z105,z2,z3,z4,z6,z843]),(0,[z0,z2,z844,z3,z4,z6]),(0,[z0,z2,z3,z151,z534,z5])],[(0,[z0,z2,z845,z4,z5,z6]),(0,[z285,z2,z3,z4,z49,z6]),(0,[z29,z0,z2,z557,z5,z6]),(0,[z0,z2,z3,z846,z4,z5]),(0,[z130,z0,z2,z4,z5,z6]),(0,[z847,z2,z3,z4,z5,z6]),(0,[z848,z0,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z72,z90]),(0,[z0,z19,z3,z4,z707,z5]),(0,[z849,z2,z3,z4,z5,z6])],[(0,[z2,z182,z9,z4,z5,z6]),(0,[z142,z2,z23,z4,z5,z6]),(0,[z0,z2,z469,z367,z5,z6]),(0,[z0,z2,z3,z850,z4,z5])],[(0,[z0,z2,z851,z4,z5,z6]),(0,[z852,z0,z2,z3,z4,z6]),(0,[z0,z853,z3,z4,z5,z6]),(0,[z186,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z141,z6]),(0,[z0,z3,z4,z735,z80,z6]),(0,[z198,z0,z2,z4,z46,z595])],[(0,[z0,z2,z854,z4,z5,z6]),(0,[z0,z2,z113,z9,z4,z5]),(0,[z338,z0,z2,z3,z4,z5]),(0,[z2,z3,z4,z5,z855,z6]),(0,[z265,z2,z4,z21,z5,z6]),(0,[z0,z2,z3,z856,z99,z6]),(0,[z0,z2,z3,z4,z573,z90])],[(0,[z167,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z93,z90]),(0,[z108,z0,z2,z3,z4,z830])]],
   [[(0,[z0,z2,z341,z4,z5,z6]),(0,[z2,z469,z9,z4,z5,z6]),(0,[z18,z0,z23,z4,z129,z5]),(0,[z11,z0,z2,z208,z4,z5]),(0,[z2,z3,z719,z77,z5,z6])],[(0,[z89,z8,z23,z4,z5,z6]),(0,[z269,z0,z9,z40,z5,z6]),(0,[z857,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z97,z90]),(0,[z0,z2,z88,z4,z5,z128])],[(0,[z25,z0,z38,z4,z5,z6]),(0,[z11,z0,z231,z3,z4,z5]),(0,[z0,z34,z777,z4,z5,z6])],[(0,[z300,z2,z9,z4,z5,z90]),(0,[z0,z2,z121,z48,z5,z6]),(1,[z2,z3,z719,z5,z6]),(0,[z0,z2,z3,z4,z858,z6]),(0,[z108,z231,z3,z4,z6,z50]),(0,[z37,z0,z2,z3,z4,z93]),(0,[z379,z0,z2,z3,z4,z280])],[(0,[z529,z133,z3,z4,z5,z6]),(0,[z443,z2,z9,z4,z5,z6]),(0,[z91,z2,z182,z4,z5,z6]),(0,[z108,z2,z3,z4,z90,z50]),(0,[z0,z2,z3,z4,z735,z6])],[(0,[z0,z2,z3,z794,z4,z5]),(0,[z76,z2,z23,z77,z5,z6]),(0,[z0,z2,z3,z4,z5,z859]),(0,[z0,z2,z4,z46,z860,z6]),(0,[z0,z2,z861,z4,z5,z6])],[(0,[z0,z862,z3,z4,z5,z6]),(0,[z863,z0,z2,z4,z5,z6]),(0,[z0,z604,z2,z3,z4,z90]),(0,[z2,z3,z4,z5,z742,z109])],[(0,[z2,z9,z4,z557,z5,z6]),(0,[z0,z2,z3,z4,z5,z864]),(0,[z865,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z150,z4,z573])]],
   [[(0,[z748,z8,z3,z4,z5,z6]),(0,[z434,z2,z9,z4,z5,z6]),(0,[z2,z23,z731,z4,z5,z6]),(0,[z0,z2,z23,z4,z5,z218]),(0,[z11,z0,z217,z3,z4,z5]),(0,[z0,z231,z3,z4,z5,z93]),(0,[z11,z0,z2,z3,z4,z247]),(0,[z0,z2,z4,z866,z5,z90])],[(0,[z0,z2,z867,z4,z5,z6]),(0,[z0,z2,z177,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z868]),(0,[z869,z2,z3,z4,z5,z6]),(0,[z0,z19,z344,z3,z4,z5]),(0,[z63,z11,z2,z3,z4,z5]),(0,[z0,z2,z3,z150,z4,z90])],[(0,[z0,z2,z870,z4,z5,z6]),(0,[z142,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z871]),(0,[z11,z0,z2,z220,z4,z5]),(0,[z0,z217,z3,z4,z5,z90]),(0,[z108,z2,z3,z4,z93,z50]),(0,[z0,z2,z517,z4,z5,z90]),(0,[z872,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z873,z6]),(0,[z379,z0,z2,z3,z4,z90]),(0,[z43,z0,z2,z3,z183,z5]),(0,[z53,z11,z2,z3,z4,z5])],[(0,[z2,z521,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z724,z5]),(0,[z0,z2,z23,z4,z181,z90]),(0,[z0,z2,z3,z4,z156,z378]),(0,[z0,z161,z3,z4,z80,z378]),(0,[z0,z2,z237,z4,z169,z238]),(0,[z92,z0,z2,z3,z31,z573])],[(0,[z2,z9,z567,z4,z5,z6]),(0,[z335,z2,z9,z4,z5,z6]),(0,[z0,z2,z23,z4,z5,z180]),(0,[z108,z2,z3,z13,z6,z50]),(1,[z0,z777,z4,z5,z6])],[(0,[z108,z2,z23,z4,z6,z50]),(0,[z0,z2,z3,z719,z5,z6]),(0,[z269,z0,z3,z39,z40,z5]),(0,[z0,z2,z3,z722,z5,z6]),(0,[z92,z0,z2,z3,z31,z90])],[(0,[z0,z2,z3,z4,z5,z874]),(0,[z2,z9,z4,z572,z5,z6]),(0,[z2,z23,z704,z4,z5,z6]),(0,[z11,z0,z34,z35,z4,z5]),(0,[z18,z0,z3,z4,z129,z5])],[(0,[z89,z8,z3,z4,z5,z6]),(0,[z242,z133,z3,z4,z5,z90]),(0,[z0,z2,z9,z4,z5,z90]),(0,[z0,z2,z3,z4,z129,z280]),(0,[z403,z2,z4,z46,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z875]),(0,[z0,z2,z202,z4,z5,z6]),(0,[z0,z2,z3,z876,z5,z6]),(0,[z0,z2,z3,z877,z5,z6]),(0,[z0,z2,z3,z4,z878,z6])],[(0,[z0,z2,z3,z13,z5,z93]),(0,[z0,z2,z879,z4,z5,z6]),(0,[z733,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z406]),(0,[z0,z2,z3,z151,z5,z204])],[(0,[z242,z133,z9,z4,z5,z6]),(0,[z0,z880,z2,z9,z4,z6]),(0,[z538,z2,z9,z4,z5,z6]),(0,[z0,z2,z23,z4,z5,z93]),(0,[z0,z2,z881,z4,z5,z6]),(0,[z0,z2,z3,z4,z882,z5]),(0,[z0,z161,z3,z4,z94,z80]),(0,[z0,z2,z3,z883,z4,z6]),(0,[z11,z0,z2,z3,z150,z4]),(0,[z0,z2,z3,z4,z163,z90])],[(0,[z412,z2,z3,z77,z5,z6]),(0,[z0,z2,z23,z4,z5,z424]),(0,[z92,z0,z2,z23,z31,z6]),(0,[z76,z2,z3,z77,z5,z6]),(0,[z0,z2,z3,z246,z5,z90]),(0,[z11,z0,z388,z2,z3,z4]),(0,[z0,z2,z884,z4,z5,z6])],[(0,[z885,z0,z2,z3,z4,z5]),(0,[z146,z2,z3,z4,z5,z742]),(0,[z146,z70,z2,z3,z4,z5]),(0,[z0,z2,z3,z886,z5,z6]),(0,[z887,z0,z2,z3,z4,z5]),(0,[z0,z2,z888,z4,z5,z90])],[(0,[z358,z0,z2,z9,z4,z5]),(0,[z0,z2,z889,z4,z5,z6]),(0,[z0,z2,z3,z890,z4,z6]),(0,[z0,z2,z3,z4,z891,z5])],[(0,[z2,z550,z9,z4,z5,z6]),(0,[z0,z2,z23,z4,z184,z90]),(0,[z892,z2,z3,z4,z5,z6]),(0,[z0,z2,z893,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z894])],[(0,[z0,z2,z220,z4,z5,z6]),(0,[z11,z0,z2,z23,z4,z5]),(0,[z108,z231,z9,z4,z5,z6]),(0,[z506,z2,z9,z4,z5,z6]),(0,[z0,z2,z323,z3,z4,z90]),(0,[z25,z11,z0,z26,z4,z5]),(1,[z819,z2,z4,z5,z6])]],
   [[(0,[z2,z9,z4,z5,z592,z6]),(0,[z11,z0,z2,z547,z4,z5]),(0,[z0,z35,z777,z4,z5,z6]),(0,[z0,z895,z3,z4,z5,z6])],[(0,[z403,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z4,z181,z90]),(0,[z0,z896,z3,z4,z5,z6]),(0,[z29,z0,z2,z627,z5,z6]),(0,[z25,z265,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z897,z6]),(0,[z0,z2,z898,z4,z5,z6])],[(0,[z108,z0,z2,z3,z246,z90]),(0,[z899,z0,z2,z3,z4,z5]),(0,[z130,z900,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z180]),(0,[z0,z2,z237,z4,z169,z6])],[(0,[z412,z0,z2,z188,z5,z6]),(0,[z108,z2,z3,z4,z6,z50]),(0,[z0,z2,z217,z3,z4,z90]),(0,[z25,z0,z512,z4,z5,z6]),(0,[z0,z2,z3,z4,z280,z56])],[(0,[z0,z2,z407,z4,z5,z6]),(0,[z901,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z902,z5,z6])],[(0,[z242,z2,z903,z4,z5,z6]),(0,[z2,z9,z4,z77,z5,z90]),(0,[z819,z2,z4,z40,z5,z6]),(0,[z0,z2,z3,z4,z860,z6])],[(0,[z91,z2,z23,z4,z5,z6]),(0,[z0,z2,z9,z904,z5,z6]),(0,[z37,z11,z0,z2,z9,z4]),(0,[z0,z2,z9,z4,z5,z595]),(0,[z0,z2,z3,z4,z5,z760]),(0,[z0,z2,z3,z4,z5,z905]),(0,[z906,z0,z2,z3,z4,z5]),(0,[z11,z0,z2,z202,z4,z5]),(0,[z0,z2,z547,z4,z5,z90]),(0,[z11,z0,z2,z3,z4,z141]),(0,[z269,z0,z3,z877,z5,z6]),(0,[z0,z3,z4,z129,z707,z5]),(1,[z0,z2,z3,z856,z6]),(0,[z0,z2,z3,z4,z534,z90])],[(0,[z763,z0,z3,z4,z5,z6]),(0,[z25,z142,z26,z4,z5,z6])]],
   [[(0,[z108,z2,z9,z13,z5,z6]),(0,[z431,z11,z2,z9,z4,z5]),(0,[z70,z2,z9,z4,z5,z6]),(0,[z0,z2,z23,z203,z4,z5]),(0,[z0,z2,z3,z4,z5,z93])],[(0,[z0,z2,z9,z31,z4,z90]),(0,[z0,z2,z3,z4,z206,z90]),(0,[z0,z2,z3,z4,z5,z907]),(0,[z0,z819,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z424]),(0,[z0,z2,z3,z124,z4,z90]),(0,[z37,z11,z0,z2,z3,z4]),(0,[z0,z2,z762,z4,z5,z6])],[(0,[z0,z2,z3,z856,z5,z6])],[(0,[z0,z2,z256,z4,z5,z6]),(0,[z0,z2,z3,z908,z5,z6]),(0,[z2,z175,z4,z49,z5,z6]),(0,[z11,z17,z2,z3,z4,z5]),(0,[z0,z2,z4,z131,z5,z90]),(0,[z0,z2,z3,z4,z5,z909]),(0,[z0,z2,z910,z4,z5,z6])],[(0,[z242,z133,z116,z4,z5,z6]),(0,[z108,z11,z2,z9,z4,z5]),(0,[z0,z19,z23,z4,z5,z56]),(0,[z265,z2,z23,z4,z5,z6]),(0,[z0,z2,z911,z4,z5,z6]),(0,[z55,z0,z3,z4,z156,z90]),(0,[z0,z2,z3,z99,z184,z424]),(0,[z0,z2,z3,z4,z184,z90])],[(0,[z0,z2,z3,z4,z246,z90]),(0,[z0,z2,z3,z4,z695,z90]),(0,[z0,z2,z3,z4,z5,z912]),(0,[z92,z0,z2,z3,z856,z6])],[(0,[z8,z9,z4,z5,z80,z6]),(0,[z0,z2,z3,z4,z5,z913])],[(0,[z2,z9,z4,z630,z5,z6]),(0,[z108,z2,z9,z4,z49,z6]),(0,[z55,z0,z9,z4,z156,z6]),(0,[z403,z2,z3,z4,z5,z6]),(0,[z68,z2,z547,z4,z5,z69]),(0,[z0,z2,z3,z4,z914,z5]),(0,[z0,z2,z3,z4,z915,z6]),(0,[z271,z0,z2,z4,z127,z5])]],
   [[(0,[z0,z2,z3,z4,z787,z6]),(0,[z0,z2,z916,z4,z5,z6]),(0,[z0,z917,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z918]),(0,[z314,z431,z2,z3,z4,z5])],[(0,[z108,z2,z919,z4,z5,z6]),(0,[z0,z2,z3,z920,z5,z6]),(0,[z0,z2,z3,z4,z212,z90]),(0,[z0,z2,z3,z778,z5,z6])],[(0,[z0,z2,z194,z4,z5,z90]),(0,[z47,z8,z3,z4,z5,z6]),(0,[z108,z0,z2,z9,z4,z90]),(0,[z0,z2,z9,z4,z280,z6]),(0,[z2,z9,z4,z5,z639,z6]),(0,[z921,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z922]),(0,[z0,z2,z3,z31,z240,z6]),(0,[z0,z2,z3,z381,z5,z527])],[(0,[z0,z2,z9,z4,z5,z377]),(0,[z2,z9,z4,z5,z205,z90]),(0,[z431,z2,z9,z4,z5,z6]),(0,[z451,z0,z2,z4,z440,z5]),(0,[z253,z2,z23,z4,z5,z6]),(0,[z11,z0,z2,z391,z4,z5]),(0,[z0,z2,z3,z4,z444,z6]),(0,[z379,z0,z479,z3,z4,z5])],[(0,[z0,z2,z3,z4,z337,z90]),(0,[z108,z2,z3,z9,z4,z90]),(0,[z0,z2,z23,z4,z5,z923]),(0,[z185,z0,z2,z3,z4,z6]),(0,[z0,z2,z924,z4,z5,z6])],[(0,[z2,z9,z38,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z796]),(0,[z0,z2,z3,z4,z5,z925]),(0,[z0,z2,z3,z4,z365,z90])],[(0,[z2,z9,z4,z646,z5,z6]),(0,[z0,z3,z4,z926,z5,z6]),(0,[z0,z2,z3,z4,z927,z6]),(0,[z0,z2,z458,z3,z4,z5]),(0,[z0,z928,z3,z4,z5,z6]),(0,[z0,z2,z3,z203,z4,z5]),(0,[z43,z0,z2,z3,z44,z5])],[(0,[z108,z2,z9,z4,z5,z6]),(0,[z108,z105,z2,z3,z4,z90]),(0,[z68,z2,z328,z4,z5,z69]),(0,[z0,z2,z237,z4,z860,z6])]],
   [[(0,[z0,z2,z9,z4,z94,z5]),(0,[z0,z2,z9,z4,z295,z6]),(0,[z217,z3,z9,z4,z5,z6]),(0,[z0,z2,z4,z929,z5,z6])],[(0,[z0,z2,z3,z930,z5,z6]),(0,[z108,z2,z3,z4,z160,z6]),(0,[z0,z2,z175,z4,z5,z90]),(1,[z0,z2,z3,z4,z816]),(0,[z0,z2,z931,z3,z4,z5])],[(0,[z0,z2,z932,z4,z5,z6]),(0,[z0,z19,z3,z4,z5,z56])],[(0,[z933,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z934,z5]),(0,[z0,z2,z3,z4,z473,z5]),(0,[z0,z2,z3,z31,z4,z424]),(0,[z935,z2,z3,z4,z5,z90])],[(0,[z8,z168,z9,z4,z5,z6]),(0,[z2,z426,z9,z4,z5,z6]),(0,[z0,z366,z3,z4,z80,z6]),(0,[z2,z936,z9,z4,z5,z6]),(0,[z2,z9,z4,z664,z5,z6]),(0,[z638,z2,z23,z4,z5,z6]),(0,[z0,z2,z536,z3,z4,z90]),(0,[z758,z0,z2,z3,z4,z90])],[(0,[z0,z2,z3,z4,z5,z937])],[(0,[z0,z2,z9,z938,z4,z5]),(0,[z656,z2,z23,z4,z5,z6]),(0,[z37,z0,z217,z3,z4,z6]),(0,[z108,z2,z182,z4,z6,z50]),(0,[z0,z2,z3,z4,z156,z90]),(0,[z0,z161,z3,z4,z80,z90]),(0,[z0,z2,z939,z4,z5,z6])],[(0,[z76,z11,z2,z3,z77,z5]),(0,[z0,z2,z3,z4,z5,z940]),(0,[z11,z0,z2,z104,z73,z5])]],
   [[(0,[z2,z9,z668,z4,z5,z6]),(0,[z16,z2,z9,z4,z5,z6]),(0,[z0,z2,z216,z4,z5,z6]),(0,[z0,z2,z3,z4,z941,z6]),(0,[z0,z34,z35,z4,z5,z6]),(0,[z942,z0,z3,z4,z5,z6])],[(0,[z2,z631,z9,z4,z5,z6]),(0,[z0,z161,z9,z4,z80,z6]),(0,[z403,z2,z237,z4,z5,z6]),(0,[z0,z2,z943,z3,z4,z5])],[(0,[z0,z2,z944,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z923]),(0,[z37,z0,z2,z3,z246,z6]),(0,[z0,z2,z945,z3,z4,z5]),(0,[z818,z2,z3,z4,z5,z6])],[(0,[z0,z2,z323,z4,z169,z6]),(0,[z0,z2,z3,z4,z827,z5])],[(0,[z89,z8,z407,z4,z5,z6]),(0,[z0,z2,z3,z4,z946,z6]),(0,[z108,z2,z202,z4,z6,z50])],[(0,[z0,z2,z3,z4,z5,z947]),(0,[z0,z2,z3,z948,z5,z6]),(0,[z485,z2,z9,z4,z5,z6]),(0,[z146,z2,z9,z4,z5,z109]),(0,[z11,z0,z2,z9,z4,z90]),(0,[z91,z2,z341,z4,z5,z6]),(0,[z0,z2,z4,z949,z5,z6]),(0,[z2,z3,z4,z49,z6,z843]),(0,[z105,z2,z3,z4,z205,z90]),(0,[z146,z0,z2,z3,z4,z141]),(0,[z25,z0,z26,z4,z5,z6]),(0,[z0,z2,z950,z4,z5,z6]),(0,[z0,z2,z3,z4,z757,z5]),(0,[z37,z0,z2,z3,z4,z573]),(0,[z0,z3,z4,z951,z5,z90])],[(0,[z0,z2,z952,z4,z5,z6]),(0,[z603,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z953]),(0,[z954,z2,z3,z4,z5,z6]),(0,[z0,z2,z844,z3,z4,z39]),(0,[z11,z0,z2,z3,z4,z293]),(0,[z0,z2,z4,z955,z5,z6])],[(0,[z0,z2,z903,z4,z5,z6]),(0,[z0,z285,z2,z3,z4,z90]),(0,[z0,z2,z3,z4,z520,z90]),(0,[z0,z2,z3,z956,z5,z6]),(0,[z11,z0,z2,z222,z3,z4])]],
   [[(0,[z0,z2,z957,z4,z5,z6]),(0,[z269,z0,z23,z40,z5,z6]),(0,[z92,z0,z2,z3,z580,z6]),(0,[z43,z0,z2,z3,z20,z5])],[(0,[z2,z903,z9,z4,z5,z6]),(0,[z198,z0,z2,z4,z432,z6]),(0,[z0,z2,z958,z4,z5,z6]),(0,[z170,z2,z391,z12,z5,z6]),(0,[z453,z2,z3,z12,z5,z6]),(0,[z0,z2,z202,z4,z5,z93]),(0,[z105,z0,z2,z175,z4,z90])],[],[(0,[z0,z2,z3,z4,z299,z90]),(0,[z11,z2,z9,z4,z49,z5]),(0,[z600,z2,z9,z4,z5,z6]),(0,[z105,z0,z2,z3,z4,z90]),(0,[z959,z0,z2,z3,z4,z5]),(0,[z0,z2,z759,z4,z5,z6]),(0,[z18,z0,z3,z4,z439,z5]),(0,[z0,z2,z960,z4,z5,z6]),(0,[z0,z2,z961,z4,z5,z90])],[(0,[z0,z2,z962,z4,z5,z6]),(0,[z2,z9,z4,z690,z5,z6]),(0,[z502,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z963]),(0,[z0,z2,z3,z4,z644,z90]),(0,[z0,z2,z964,z4,z5,z6])],[(0,[z0,z965,z3,z4,z5,z6]),(0,[z105,z0,z2,z177,z4,z90]),(0,[z431,z2,z3,z4,z5,z69]),(0,[z0,z2,z3,z4,z966,z6])],[(0,[z686,z2,z9,z4,z5,z6]),(1,[z217,z9,z4,z5,z6]),(0,[z453,z2,z9,z4,z5,z6]),(0,[z0,z2,z23,z4,z5,z967]),(0,[z0,z2,z23,z151,z5,z204]),(0,[z2,z3,z4,z5,z6,z843]),(0,[z0,z3,z877,z40,z5,z6]),(1,[z0,z3,z4,z707,z5]),(0,[z63,z2,z3,z4,z5,z90])],[(0,[z170,z2,z3,z719,z5,z6]),(0,[z509,z0,z2,z3,z4,z90]),(0,[z0,z22,z3,z877,z5,z6]),(0,[z0,z2,z104,z73,z5,z6]),(0,[z0,z2,z4,z757,z5,z6])]],
   [[(0,[z300,z11,z2,z9,z4,z5]),(0,[z0,z2,z3,z4,z5,z968])],[(0,[z0,z2,z936,z4,z5,z6]),(0,[z0,z2,z4,z969,z5,z6]),(0,[z0,z2,z3,z4,z970,z5]),(0,[z971,z2,z3,z4,z5,z6])],[(0,[z0,z2,z23,z972,z4,z5]),(0,[z2,z3,z4,z5,z792,z90])],[(0,[z0,z973,z3,z4,z5,z6]),(0,[z0,z217,z3,z13,z5,z6]),(0,[z108,z11,z2,z3,z4,z50])],[(0,[z0,z2,z974,z4,z5,z6]),(0,[z147,z8,z3,z4,z5,z6]),(0,[z170,z2,z9,z77,z5,z6]),(0,[z0,z2,z712,z4,z5,z6]),(0,[z158,z0,z2,z3,z4,z90])],[(0,[z0,z2,z9,z4,z573,z5]),(0,[z0,z2,z3,z13,z5,z90]),(1,[z0,z2,z708,z5,z6])],[(0,[z269,z0,z3,z40,z5,z6]),(0,[z900,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z381,z184,z6]),(0,[z43,z0,z2,z3,z778,z5]),(0,[z0,z2,z975,z4,z5,z6])],[(0,[z0,z2,z3,z976,z5,z6]),(0,[z0,z2,z3,z4,z5,z977]),(0,[z89,z11,z8,z3,z4,z5]),(1,[z2,z9,z246,z5,z6]),(0,[z0,z2,z9,z150,z4,z6]),(0,[z0,z2,z3,z978,z4,z6]),(0,[z11,z0,z2,z517,z4,z5]),(0,[z17,z2,z3,z4,z5,z90]),(0,[z0,z2,z458,z3,z4,z90]),(0,[z0,z2,z3,z778,z5,z204])]],
   [[(0,[z531,z0,z2,z3,z4,z90]),(0,[z0,z217,z9,z4,z5,z6]),(0,[z0,z2,z9,z13,z5,z6]),(0,[z29,z0,z2,z21,z5,z90])],[(0,[z412,z0,z2,z21,z5,z6]),(0,[z0,z2,z23,z4,z979,z5]),(0,[z0,z2,z23,z4,z980,z6]),(0,[z108,z2,z175,z4,z5,z6]),(0,[z2,z3,z4,z6,z843,z50]),(0,[z981,z2,z3,z4,z5,z6]),(0,[z982,z2,z3,z4,z5,z6]),(0,[z697,z0,z2,z3,z4,z90]),(0,[z0,z2,z3,z4,z444,z204])],[(0,[z47,z0,z26,z4,z5,z6]),(0,[z2,z23,z425,z4,z5,z6]),(0,[z11,z0,z2,z216,z4,z5]),(0,[z0,z2,z3,z4,z342,z90]),(0,[z0,z34,z4,z126,z5,z6]),(0,[z983,z2,z3,z4,z5,z6]),(0,[z0,z2,z931,z3,z4,z90]),(0,[z0,z2,z3,z4,z504,z90]),(0,[z0,z2,z984,z4,z5,z6])],[(0,[z300,z2,z9,z4,z5,z6]),(0,[z358,z0,z2,z23,z4,z5]),(0,[z0,z2,z437,z4,z181,z6]),(0,[z108,z0,z231,z3,z4,z90]),(0,[z0,z2,z985,z4,z5,z6]),(0,[z358,z0,z2,z4,z131,z5]),(0,[z0,z2,z986,z4,z5,z6]),(0,[z0,z2,z458,z3,z4,z295]),(0,[z0,z2,z165,z4,z757,z5])],[(0,[z0,z2,z987,z4,z5,z6]),(0,[z2,z116,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z967]),(0,[z0,z217,z3,z246,z5,z6]),(1,[z0,z2,z4,z860,z6]),(0,[z403,z2,z437,z4,z5,z6]),(0,[z11,z0,z2,z964,z4,z5])],[(0,[z2,z9,z4,z65,z5,z6]),(0,[z2,z3,z12,z719,z5,z6]),(0,[z108,z2,z3,z4,z218,z50]),(0,[z0,z2,z3,z4,z5,z988]),(0,[z0,z989,z3,z4,z5,z6])],[(0,[z11,z0,z2,z116,z4,z5]),(0,[z108,z2,z9,z4,z5,z218]),(0,[z272,z2,z9,z4,z5,z90]),(0,[z0,z2,z73,z708,z5,z6])],[(0,[z0,z2,z73,z144,z5,z6]),(0,[z0,z2,z3,z4,z5,z990]),(0,[z0,z2,z3,z4,z5,z991]),(0,[z198,z0,z2,z4,z860,z6]),(0,[z11,z0,z2,z3,z298,z4])]],
   [[(0,[z242,z2,z194,z4,z5,z6]),(0,[z0,z2,z3,z972,z4,z5]),(0,[z11,z0,z2,z182,z4,z5]),(0,[z0,z2,z3,z992,z4,z5]),(0,[z11,z0,z2,z3,z99,z184])],[(0,[z0,z2,z3,z4,z5,z993]),(0,[z0,z2,z9,z246,z5,z6]),(0,[z698,z2,z9,z4,z5,z6]),(0,[z0,z2,z391,z4,z5,z6]),(0,[z994,z0,z2,z4,z5,z6]),(0,[z108,z0,z217,z3,z4,z90]),(0,[z0,z2,z3,z995,z5,z6]),(0,[z0,z482,z3,z4,z156,z6]),(0,[z0,z2,z3,z708,z5,z6]),(0,[z0,z2,z3,z820,z5,z90])],[(0,[z2,z8,z9,z4,z5,z90]),(0,[z0,z2,z996,z3,z4,z5]),(0,[z0,z2,z517,z4,z5,z6]),(0,[z0,z2,z3,z4,z997,z5]),(0,[z0,z2,z3,z4,z5,z998]),(0,[z130,z11,z0,z2,z4,z5]),(0,[z11,z0,z2,z4,z131,z5]),(0,[z29,z0,z2,z708,z5,z6]),(0,[z0,z2,z3,z44,z4,z444])],[(0,[z68,z2,z9,z4,z5,z69]),(0,[z0,z2,z3,z999,z5,z6]),(0,[z0,z2,z1000,z4,z5,z6]),(0,[z1001,z2,z3,z4,z5,z6]),(0,[z0,z2,z1002,z3,z4,z5])],[(0,[z2,z558,z9,z4,z5,z6]),(0,[z76,z2,z216,z77,z5,z6]),(0,[z55,z11,z0,z3,z4,z156]),(0,[z0,z2,z3,z4,z1003,z5]),(0,[z37,z758,z0,z2,z3,z4])],[(0,[z185,z0,z2,z3,z4,z93]),(0,[z92,z0,z2,z3,z31,z6]),(0,[z296,z0,z3,z4,z439,z5])],[(0,[z0,z2,z3,z4,z1004,z5])],[(0,[z242,z133,z3,z4,z5,z6]),(0,[z0,z2,z1005,z4,z5,z6]),(0,[z779,z0,z2,z3,z5,z6]),(0,[z0,z285,z2,z4,z46,z6]),(0,[z0,z2,z23,z4,z5,z436]),(0,[z0,z2,z3,z4,z979,z5]),(0,[z0,z2,z3,z4,z980,z6]),(0,[z11,z0,z2,z175,z4,z5]),(0,[z105,z0,z2,z3,z4,z377]),(0,[z0,z2,z3,z1006,z5,z6]),(0,[z265,z34,z2,z4,z5,z6]),(0,[z0,z115,z3,z4,z5,z56]),(0,[z0,z2,z3,z150,z151,z204])]],
   [[(0,[z108,z2,z9,z4,z5,z93]),(0,[z0,z34,z168,z4,z5,z6]),(0,[z0,z2,z23,z4,z444,z6]),(0,[z0,z2,z3,z4,z5,z1007]),(0,[z0,z2,z1008,z4,z5,z6]),(0,[z0,z161,z3,z4,z735,z6])],[(0,[z1009,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z40,z816]),(0,[z11,z0,z2,z237,z4,z169]),(0,[z198,z403,z2,z4,z46,z6]),(0,[z0,z2,z4,z127,z757,z5])],[(0,[z2,z23,z470,z4,z5,z6]),(0,[z0,z2,z165,z4,z5,z566]),(0,[z0,z2,z23,z113,z4,z5]),(0,[z0,z2,z1010,z4,z5,z6]),(0,[z1011,z2,z3,z4,z5,z6])],[(0,[z0,z2,z1012,z4,z5,z6]),(0,[z2,z9,z4,z5,z123,z6]),(0,[z788,z0,z2,z3,z4,z5]),(0,[z11,z0,z2,z177,z4,z5]),(0,[z272,z105,z2,z3,z4,z90]),(0,[z1013,z2,z3,z4,z5,z6]),(0,[z0,z22,z3,z78,z5,z90]),(0,[z0,z115,z3,z4,z80,z90]),(0,[z758,z0,z2,z3,z4,z59]),(0,[z505,z0,z2,z4,z140,z5])],[(0,[z0,z2,z116,z4,z5,z90]),(0,[z0,z2,z9,z4,z39,z5])],[(0,[z11,z0,z2,z407,z4,z5]),(0,[z0,z2,z1014,z4,z5,z6]),(0,[z11,z0,z2,z256,z4,z5]),(0,[z0,z2,z3,z4,z301,z90]),(0,[z0,z2,z777,z4,z5,z6]),(0,[z0,z1015,z3,z4,z5,z90])],[(0,[z0,z22,z9,z78,z5,z6]),(0,[z0,z2,z23,z4,z5,z378]),(0,[z55,z0,z23,z4,z156,z6]),(0,[z0,z2,z23,z4,z432,z90]),(0,[z1016,z0,z2,z4,z5,z6])],[(0,[z189,z2,z9,z4,z5,z6]),(0,[z2,z3,z9,z246,z5,z6]),(0,[z130,z0,z2,z4,z5,z90]),(0,[z1017,z0,z2,z4,z5,z6]),(0,[z11,z0,z2,z1018,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z5,z1019]),(0,[z343,z2,z9,z4,z5,z6]),(0,[z108,z0,z2,z23,z4,z90]),(0,[z0,z2,z23,z4,z473,z5]),(0,[z108,z2,z3,z4,z6,z843])],[(0,[z0,z2,z9,z4,z59,z90]),(0,[z0,z2,z797,z3,z4,z6]),(0,[z0,z2,z23,z4,z280,z6]),(0,[z198,z0,z2,z113,z4,z46])],[(0,[z55,z0,z3,z4,z337,z6]),(0,[z0,z1020,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z141,z90]),(0,[z269,z11,z0,z3,z40,z5]),(0,[z0,z2,z3,z4,z466,z90])],[(0,[z0,z2,z23,z4,z156,z90]),(0,[z2,z3,z4,z5,z855,z90])],[(0,[z2,z216,z4,z77,z5,z6]),(0,[z0,z2,z786,z4,z5,z6]),(0,[z11,z0,z2,z328,z4,z5]),(0,[z0,z2,z1021,z4,z5,z6]),(0,[z0,z2,z84,z4,z127,z5])],[(0,[z0,z2,z9,z4,z141,z6]),(0,[z419,z0,z2,z3,z4,z90]),(0,[z819,z2,z3,z4,z5,z6]),(0,[z0,z2,z1022,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z436])],[(0,[z239,z2,z9,z4,z5,z6]),(0,[z1023,z0,z2,z4,z5,z6]),(0,[z2,z323,z9,z4,z49,z6]),(0,[z0,z2,z4,z1024,z5,z6]),(0,[z0,z2,z121,z73,z5,z6]),(0,[z0,z2,z547,z4,z5,z6]),(0,[z0,z2,z1025,z4,z5,z6]),(0,[z1026,z2,z3,z4,z5,z6]),(0,[z1027,z2,z3,z4,z5,z6]),(0,[z0,z2,z1028,z4,z5,z6]),(0,[z0,z2,z3,z31,z4,z90])],[(0,[z242,z748,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1029,z6]),(0,[z0,z2,z23,z4,z94,z5]),(0,[z0,z2,z23,z4,z295,z6]),(0,[z1030,z0,z2,z3,z4,z5]),(0,[z108,z0,z2,z202,z4,z90]),(0,[z1031,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z44,z778,z5])]],
   [[(0,[z0,z2,z793,z4,z5,z6]),(0,[z29,z11,z0,z2,z21,z5]),(0,[z0,z2,z3,z4,z1032,z5]),(0,[z0,z2,z3,z113,z4,z5]),(0,[z0,z2,z3,z1033,z4,z5]),(0,[z158,z0,z2,z3,z4,z444])],[(0,[z0,z2,z3,z4,z1034,z6]),(0,[z0,z2,z3,z4,z414,z90]),(0,[z0,z2,z1035,z3,z4,z5]),(0,[z0,z2,z4,z860,z169,z6])],[(0,[z0,z2,z317,z4,z5,z243]),(0,[z170,z2,z216,z4,z5,z6]),(0,[z0,z2,z3,z1036,z5,z6]),(0,[z105,z2,z3,z4,z49,z90]),(0,[z0,z2,z3,z4,z5,z816]),(0,[z147,z0,z2,z3,z4,z90])],[(0,[z11,z0,z2,z194,z4,z5]),(0,[z0,z255,z168,z4,z5,z6]),(0,[z0,z2,z643,z3,z4,z90])],[(0,[z2,z731,z9,z4,z5,z6]),(0,[z610,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z432,z90]),(0,[z68,z2,z3,z4,z5,z205]),(0,[z0,z2,z3,z4,z5,z378]),(0,[z55,z0,z3,z4,z156,z6]),(0,[z0,z19,z3,z4,z302,z5]),(1,[z0,z2,z4,z757,z5])],[(0,[z105,z2,z9,z4,z49,z6]),(0,[z0,z217,z182,z4,z5,z6]),(0,[z0,z2,z3,z1037,z4,z5]),(0,[z0,z3,z4,z439,z80,z90])],[(0,[z0,z2,z328,z4,z5,z6]),(0,[z338,z0,z2,z9,z4,z5]),(0,[z0,z2,z3,z1038,z5,z6]),(0,[z0,z2,z177,z4,z5,z90]),(0,[z1039,z2,z3,z4,z5,z6]),(0,[z92,z11,z0,z2,z3,z31])],[(0,[z0,z2,z182,z4,z5,z90]),(0,[z142,z2,z3,z4,z5,z90]),(0,[z269,z0,z131,z40,z5,z6]),(0,[z0,z2,z4,z1040,z5,z6]),(0,[z0,z2,z3,z4,z280,z6]),(0,[z0,z19,z3,z4,z280,z56]),(0,[z11,z265,z2,z3,z4,z5]),(0,[z0,z2,z165,z260,z4,z5])]],
   [[(0,[z0,z2,z1041,z4,z5,z6]),(0,[z0,z161,z23,z4,z80,z6]),(0,[z0,z2,z3,z4,z5,z377]),(0,[z0,z2,z3,z4,z5,z1042])],[(0,[z0,z2,z3,z4,z332,z90]),(0,[z130,z0,z2,z4,z39,z5]),(0,[z55,z0,z458,z3,z4,z156])],[(0,[z0,z2,z194,z4,z5,z6]),(0,[z0,z2,z3,z1043,z5,z6]),(0,[z108,z37,z2,z9,z4,z6]),(0,[z47,z0,z262,z4,z5,z6])],[(0,[z2,z9,z4,z5,z205,z6]),(0,[z170,z2,z3,z355,z5,z6]),(0,[z11,z0,z2,z23,z4,z90]),(0,[z0,z2,z237,z4,z181,z6]),(0,[z0,z1044,z3,z4,z5,z6]),(0,[z0,z217,z202,z4,z5,z6]),(0,[z142,z2,z426,z4,z5,z6]),(0,[z1045,z2,z3,z4,z5,z6]),(0,[z0,z3,z777,z4,z5,z6]),(0,[z0,z2,z1046,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z280]),(0,[z0,z2,z3,z1047,z4,z5])],[(0,[z89,z8,z3,z4,z5,z90]),(0,[z146,z2,z23,z4,z5,z109]),(0,[z0,z2,z1048,z4,z5,z6]),(0,[z0,z2,z1049,z4,z5,z6])],[(0,[z0,z2,z3,z1050,z5,z6]),(0,[z0,z2,z3,z1051,z5,z6]),(0,[z0,z2,z202,z4,z5,z90]),(0,[z0,z2,z3,z4,z94,z5]),(0,[z0,z2,z3,z4,z295,z6]),(0,[z0,z19,z3,z4,z295,z56])],[(0,[z0,z366,z2,z3,z4,z90]),(0,[z0,z308,z426,z4,z5,z6]),(0,[z0,z2,z1052,z4,z5,z6]),(0,[z0,z2,z182,z246,z5,z6]),(0,[z11,z0,z2,z3,z13,z5]),(0,[z1053,z2,z3,z4,z5,z6]),(0,[z1054,z0,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1055]),(0,[z360,z2,z9,z4,z5,z6]),(1,[z0,z217,z3,z4,z90]),(0,[z0,z2,z3,z4,z455,z90]),(0,[z0,z2,z1056,z4,z5,z6])]],
   [[(0,[z242,z2,z9,z4,z5,z6]),(0,[z2,z9,z4,z215,z5,z6]),(0,[z0,z2,z208,z4,z5,z90]),(0,[z76,z2,z3,z77,z5,z90]),(0,[z1057,z2,z3,z4,z5,z6]),(0,[z1058,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z597])],[(0,[z0,z2,z175,z4,z5,z6]),(0,[z0,z217,z3,z4,z5,z218]),(0,[z0,z1059,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z461,z90]),(0,[z0,z2,z3,z4,z1060,z5]),(0,[z198,z0,z2,z4,z46,z6])],[],[(0,[z0,z2,z3,z938,z4,z5]),(0,[z2,z23,z9,z4,z5,z90]),(0,[z170,z2,z936,z4,z5,z6]),(1,[z0,z2,z3,z246,z90]),(0,[z1061,z0,z2,z3,z4,z5]),(0,[z935,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z856,z4,z6])],[(0,[z0,z2,z3,z4,z5,z1062]),(0,[z0,z2,z220,z4,z5,z90]),(0,[z1063,z0,z2,z3,z4,z5]),(0,[z0,z2,z202,z246,z5,z6]),(0,[z0,z2,z3,z4,z1064,z5]),(0,[z11,z403,z2,z3,z4,z5]),(0,[z758,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z1065]),(0,[z0,z2,z3,z4,z5,z1066]),(0,[z338,z105,z2,z3,z4,z49]),(0,[z0,z3,z4,z877,z5,z6]),(0,[z130,z358,z0,z2,z4,z5]),(0,[z0,z2,z708,z21,z5,z6]),(0,[z0,z2,z3,z4,z111,z90])],[(0,[z0,z2,z9,z4,z5,z218]),(0,[z11,z142,z2,z3,z4,z5]),(0,[z0,z161,z3,z4,z80,z6]),(0,[z0,z2,z3,z622,z4,z90]),(0,[z11,z0,z2,z3,z4,z295])],[(0,[z242,z133,z220,z4,z5,z6]),(0,[z170,z2,z3,z12,z5,z90]),(0,[z0,z231,z3,z4,z5,z90]),(0,[z0,z2,z1067,z4,z5,z6])]],
   [[(0,[z300,z2,z731,z4,z5,z6]),(0,[z574,z2,z9,z4,z5,z6]),(0,[z0,z2,z1068,z4,z5,z6]),(0,[z0,z2,z3,z4,z1069,z6]),(0,[z689,z0,z2,z3,z4,z90])],[(0,[z1070,z2,z3,z4,z5,z6]),(0,[z368,z0,z2,z3,z534,z5])],[(1,[z2,z731,z4,z5,z6]),(0,[z170,z2,z9,z12,z5,z6]),(0,[z0,z231,z9,z4,z5,z6]),(0,[z0,z2,z3,z246,z5,z218]),(0,[z146,z2,z3,z4,z5,z109]),(0,[z53,z2,z3,z4,z5,z90]),(0,[z0,z115,z3,z4,z5,z139])],[(0,[z11,z2,z8,z9,z4,z5]),(0,[z0,z2,z1071,z3,z4,z5]),(0,[z2,z217,z9,z4,z5,z6]),(0,[z2,z919,z9,z4,z5,z6]),(0,[z514,z2,z9,z4,z5,z6]),(0,[z91,z2,z23,z4,z5,z90]),(0,[z697,z2,z3,z77,z5,z6]),(0,[z434,z0,z2,z3,z4,z90]),(0,[z0,z2,z3,z4,z486,z90]),(0,[z198,z11,z0,z2,z4,z46])],[(0,[z1072,z0,z2,z3,z4,z5]),(0,[z170,z2,z9,z4,z5,z90]),(0,[z885,z0,z2,z9,z4,z5]),(0,[z0,z9,z4,z926,z5,z6]),(0,[z63,z2,z9,z4,z5,z6]),(0,[z0,z2,z1018,z4,z5,z6])],[(0,[z2,z121,z9,z77,z5,z6]),(0,[z0,z2,z9,z4,z80,z90]),(0,[z385,z2,z9,z4,z5,z6]),(0,[z53,z2,z9,z4,z5,z6]),(0,[z265,z2,z104,z4,z5,z6]),(0,[z0,z3,z4,z951,z5,z6]),(0,[z0,z2,z3,z4,z155,z90])],[(0,[z91,z2,z731,z4,z5,z6]),(0,[z0,z2,z23,z150,z4,z6]),(0,[z0,z231,z3,z246,z5,z6]),(1,[z2,z3,z4,z6,z843]),(0,[z105,z2,z3,z4,z49,z377]),(1,[z2,z3,z4,z5,z742]),(0,[z0,z2,z931,z3,z4,z156])],[(0,[z0,z2,z323,z9,z4,z90]),(0,[z0,z1073,z3,z4,z5,z6]),(0,[z0,z217,z23,z4,z5,z6]),(0,[z185,z68,z2,z3,z4,z69]),(0,[z0,z2,z1074,z4,z5,z6])]],
   [[(0,[z242,z8,z9,z4,z5,z6]),(0,[z2,z23,z411,z4,z5,z6]),(0,[z0,z2,z3,z151,z444,z204])],[(0,[z0,z2,z23,z4,z5,z90]),(0,[z119,z0,z2,z3,z20,z5])],[],[(0,[z108,z2,z9,z4,z6,z90]),(0,[z0,z2,z9,z4,z5,z238]),(0,[z0,z2,z961,z4,z5,z6])],[(0,[z242,z133,z23,z4,z5,z6]),(0,[z0,z2,z731,z4,z5,z6]),(0,[z0,z2,z9,z4,z798,z6]),(0,[z0,z2,z3,z77,z184,z90]),(0,[z0,z2,z1075,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1076]),(0,[z0,z2,z9,z799,z4,z6]),(0,[z17,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z4,z1077,z6]),(0,[z269,z358,z0,z3,z40,z5])],[(0,[z11,z2,z9,z4,z77,z5]),(0,[z548,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z44,z229,z5])],[(0,[z2,z9,z4,z5,z282,z6]),(0,[z91,z217,z3,z4,z5,z6]),(0,[z0,z2,z1078,z4,z5,z6]),(0,[z105,z2,z175,z4,z49,z6]),(0,[z0,z2,z3,z4,z5,z1079]),(1,[z0,z2,z3,z778,z5])]],
   [[(0,[z0,z2,z23,z246,z5,z6]),(0,[z0,z2,z3,z4,z6,z843]),(0,[z0,z2,z3,z4,z5,z742]),(0,[z0,z2,z3,z4,z1080,z6]),(0,[z0,z2,z3,z4,z816,z6])],[(0,[z0,z2,z3,z4,z5,z1081])],[(0,[z89,z8,z194,z4,z5,z6]),(0,[z47,z8,z9,z4,z5,z6]),(0,[z0,z880,z2,z3,z4,z6]),(0,[z706,z2,z23,z4,z5,z6]),(0,[z0,z2,z165,z4,z5,z128])],[(0,[z0,z2,z1082,z4,z5,z6]),(0,[z0,z2,z1083,z4,z5,z6]),(0,[z0,z2,z1084,z4,z5,z6]),(0,[z0,z3,z4,z156,z80,z90]),(0,[z0,z2,z4,z866,z5,z6]),(0,[z0,z2,z4,z860,z5,z6]),(0,[z272,z2,z3,z4,z5,z532])],[(0,[z0,z2,z919,z4,z5,z6]),(0,[z0,z3,z4,z707,z5,z56]),(0,[z95,z0,z2,z3,z4,z90]),(0,[z0,z2,z3,z150,z4,z6])],[(0,[z0,z217,z3,z4,z5,z6]),(0,[z0,z1085,z2,z3,z4,z6]),(0,[z2,z250,z9,z4,z5,z6]),(0,[z0,z764,z2,z3,z4,z6]),(0,[z358,z0,z2,z3,z4,z5]),(0,[z0,z3,z78,z877,z5,z6])],[(0,[z0,z2,z3,z4,z1086,z6]),(0,[z1087,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1088,z6]),(0,[z265,z2,z469,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z90]),(0,[z0,z2,z3,z1089,z4,z5]),(0,[z55,z0,z3,z4,z156,z180]),(0,[z0,z2,z3,z4,z707,z5]),(0,[z265,z2,z3,z4,z5,z90]),(0,[z11,z758,z0,z2,z3,z4])]],
   [[(0,[z91,z2,z3,z246,z5,z6]),(0,[z0,z2,z23,z4,z5,z595]),(0,[z29,z0,z2,z21,z5,z6]),(0,[z0,z2,z3,z4,z1090,z5])],[(0,[z89,z748,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1091,z6]),(0,[z0,z2,z1092,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1093])],[(0,[z0,z2,z9,z4,z5,z6]),(0,[z265,z2,z9,z4,z5,z6]),(0,[z2,z9,z4,z49,z5,z90]),(0,[z0,z19,z9,z4,z5,z56]),(0,[z1094,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z99,z184,z90])],[(0,[z0,z2,z23,z4,z39,z5]),(0,[z0,z2,z23,z31,z4,z90]),(0,[z0,z2,z3,z4,z5,z1095]),(0,[z11,z0,z161,z3,z4,z80])],[(0,[z11,z0,z2,z3,z4,z5]),(0,[z185,z0,z2,z9,z4,z6]),(0,[z0,z2,z1096,z4,z5,z6]),(0,[z0,z2,z1097,z4,z5,z6]),(0,[z170,z11,z2,z3,z12,z5]),(0,[z0,z2,z3,z261,z4,z90]),(0,[z0,z2,z3,z1098,z4,z5]),(0,[z0,z2,z1099,z4,z5,z6]),(0,[z0,z2,z1100,z4,z5,z6])],[(0,[z0,z2,z1101,z4,z5,z6]),(0,[z0,z2,z9,z99,z184,z6]),(0,[z0,z2,z3,z4,z1102,z5]),(0,[z0,z2,z3,z4,z543,z90])],[(0,[z1103,z0,z2,z3,z4,z5]),(0,[z0,z1104,z2,z3,z4,z6]),(0,[z0,z2,z458,z9,z4,z5]),(0,[z43,z0,z2,z9,z44,z5]),(0,[z272,z2,z9,z4,z5,z6]),(0,[z0,z2,z3,z246,z5,z6]),(0,[z0,z1105,z3,z4,z5,z6]),(0,[z11,z0,z22,z3,z78,z5])],[(0,[z17,z2,z116,z4,z5,z6]),(0,[z0,z2,z3,z1106,z4,z5]),(0,[z1107,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z856,z184,z6]),(0,[z839,z2,z3,z4,z5,z90]),(0,[z0,z2,z888,z4,z5,z6])]],
   [[(0,[z0,z2,z23,z4,z59,z90]),(0,[z1108,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1109]),(0,[z0,z2,z3,z4,z5,z1110]),(0,[z0,z2,z1111,z4,z5,z6])],[(0,[z0,z2,z3,z4,z283,z90]),(0,[z0,z2,z3,z668,z184,z6]),(0,[z108,z0,z2,z182,z4,z90]),(0,[z0,z2,z3,z4,z5,z830])],[(0,[z133,z748,z3,z4,z5,z6]),(0,[z0,z2,z1112,z4,z5,z6]),(0,[z0,z1113,z3,z4,z5,z6])],[(0,[z0,z2,z323,z4,z6,z227]),(1,[z0,z3,z4,z735,z6]),(0,[z11,z0,z2,z3,z4,z577]),(0,[z1114,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z955,z5,z90])],[(0,[z0,z2,z3,z4,z396,z90]),(0,[z0,z1115,z3,z4,z5,z6]),(0,[z0,z2,z1116,z4,z5,z6]),(0,[z0,z2,z3,z381,z5,z204]),(0,[z158,z0,z2,z3,z229,z5])],[(0,[z0,z2,z1117,z4,z5,z6]),(0,[z285,z2,z9,z4,z49,z6]),(0,[z0,z2,z23,z4,z5,z377]),(0,[z0,z2,z3,z4,z642,z90]),(0,[z68,z0,z2,z3,z4,z141]),(0,[z0,z2,z4,z1118,z5,z6]),(0,[z681,z0,z2,z3,z4,z90]),(0,[z11,z0,z2,z975,z4,z5])],[(0,[z0,z2,z3,z904,z5,z6]),(0,[z91,z2,z116,z4,z5,z6]),(0,[z11,z242,z2,z9,z4,z5]),(0,[z1119,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z595]),(0,[z1120,z2,z3,z4,z5,z6]),(0,[z431,z0,z2,z3,z4,z90])],[(0,[z0,z133,z3,z4,z80,z90]),(0,[z2,z9,z4,z346,z5,z6]),(0,[z0,z2,z3,z4,z5,z1121]),(0,[z0,z231,z182,z4,z5,z6]),(0,[z0,z2,z3,z4,z80,z378])]],
   [[(0,[z2,z9,z4,z77,z5,z6]),(0,[z11,z70,z2,z9,z4,z5]),(0,[z316,z2,z9,z4,z5,z6]),(0,[z0,z2,z341,z4,z5,z90]),(0,[z0,z2,z3,z4,z533,z90])],[(0,[z63,z2,z182,z4,z5,z6]),(0,[z0,z2,z3,z4,z39,z5]),(0,[z18,z0,z2,z3,z4,z444]),(0,[z0,z2,z3,z645,z4,z90]),(0,[z0,z2,z1122,z4,z5,z6])],[(0,[z0,z2,z3,z1123,z5,z6]),(0,[z0,z2,z3,z4,z1124,z5]),(0,[z108,z0,z2,z3,z4,z90]),(0,[z0,z2,z3,z4,z5,z1125]),(0,[z0,z2,z3,z4,z1126,z5]),(0,[z0,z2,z3,z151,z4,z280])],[(0,[z37,z0,z2,z458,z3,z4]),(0,[z0,z2,z3,z4,z5,z1127])],[(0,[z0,z2,z116,z4,z5,z6]),(0,[z2,z9,z4,z246,z5,z6]),(0,[z338,z0,z2,z23,z4,z5]),(0,[z0,z2,z104,z708,z5,z6]),(0,[z0,z2,z104,z73,z5,z90]),(0,[z0,z2,z3,z4,z775,z5]),(0,[z0,z2,z3,z31,z856,z6])],[(0,[z2,z9,z4,z359,z5,z6]),(0,[z0,z2,z3,z4,z5,z1128]),(0,[z0,z1015,z3,z4,z5,z6]),(0,[z428,z0,z2,z260,z4,z5])],[(0,[z0,z2,z1129,z4,z5,z6]),(0,[z142,z2,z35,z4,z5,z6]),(0,[z0,z2,z4,z131,z5,z6]),(0,[z0,z2,z3,z1130,z5,z6]),(0,[z29,z265,z2,z21,z5,z6]),(0,[z0,z2,z3,z4,z581,z90]),(0,[z0,z2,z3,z568,z4,z90]),(0,[z0,z2,z3,z778,z151,z5]),(0,[z0,z2,z3,z4,z59,z90])],[(0,[z0,z285,z2,z9,z4,z90]),(1,[z0,z3,z877,z5,z6]),(0,[z0,z2,z3,z4,z583,z90]),(0,[z0,z2,z3,z1131,z4,z5]),(0,[z815,z2,z3,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 509).take 503) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1012).take 314) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1326)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [509, 503, 314] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 69).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 69).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 141).take 66).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 207).take 49).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [69, 72, 66, 49] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_43960

theorem PEqualNP.Outside.L_meta_43960 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276797568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276797568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43960.solve
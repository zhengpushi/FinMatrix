(* 
   purpose  : examples for a paper (deadline at 2024/05/22)
   author   : ZhengPu Shi
   date     : 2024.05.20
 *)

From FinMatrix Require MatrixQc MatrixR.

(* More examples for a paper in 2024/05/22 *)

(* CASE 2: Compute inverse matrix of a matrix which contain decimal numbers *)
Section CASE2.
  Import MatrixQc.

  (* create random data in MATLAB by command ">> rand(10,10)" *)
  Let M :=
        Q2Qc_dlist
        [[0.8147;0.1576;0.6557;0.7060;0.4387;0.2760;0.7513;0.8407;0.3517;0.0759];
         [0.9058;0.9706;0.0357;0.0318;0.3816;0.6797;0.2551;0.2543;0.8308;0.0540];
         [0.1270;0.9572;0.8491;0.2769;0.7655;0.6551;0.5060;0.8143;0.5853;0.5308];
         [0.9134;0.4854;0.9340;0.0462;0.7952;0.1626;0.6991;0.2435;0.5497;0.7792];
         [0.6324;0.8003;0.6787;0.0971;0.1869;0.1190;0.8909;0.9293;0.9172;0.9340];
         [0.0975;0.1419;0.7577;0.8235;0.4898;0.4984;0.9593;0.3500;0.2858;0.1299];
         [0.2785;0.4218;0.7431;0.6948;0.4456;0.9597;0.5472;0.1966;0.7572;0.5688];
         [0.5469;0.9157;0.3922;0.3171;0.6463;0.3404;0.1386;0.2511;0.7537;0.4694];
         [0.9575;0.7922;0.6555;0.9502;0.7094;0.5853;0.1493;0.6160;0.3804;0.0119];
         [0.9649;0.9595;0.1712;0.0344;0.7547;0.2238;0.2575;0.4733;0.5678;0.3371]].

  (* Time Compute minvListGE 7 M. *)
  (* Time Compute minvListAM 7 M. *)

  (* Note that, the Qc type has extra proof informations, which should be dropped *)
End CASE2.

(* CASE 3: Compute inverse matrix of a matrix which is symbolic *)
Section CASE3.
  Import MatrixR.
  Variable θ ϕ : R.
  Notation sθ := (sin θ). Notation cθ := (cos θ).
  Notation sϕ := (sin ϕ). Notation cϕ := (cos ϕ).

  (* Given input matrix *)
  Let M : smat 3 := l2m [[1;0;-sθ];[0;cϕ;cθ*sϕ];[0;-sϕ;cθ*cϕ]]%R.

  (* A unknown inverse matrix *)
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
  Let M' : smat 3 := l2m [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  
  (* Find inverse matrix *)
  Goal minvNoCheck M = M'.
  Proof.
    meq; field_simplify; autorewrite with R. 
    all:
    match goal with
    | |- ?a = ?b => idtac
    | |- ?a <> ?b => try admit
    end.
    (* now, we find a preliminary formulas: *)
    (*
  1 = a11

goal 2 (ID 4122) is:
 sϕ * sθ / cθ = a12
goal 3 (ID 4128) is:
 cϕ * sθ / cθ = a13
goal 4 (ID 4132) is:
 0 = a21
goal 5 (ID 4139) is:
 cϕ * cθ / cθ = a22
goal 6 (ID 4147) is:
 (- (cθ * sϕ / cθ))%R = a23
goal 7 (ID 4151) is:
 0 = a31
goal 8 (ID 4158) is:
 sϕ / cθ = a32
goal 9 (ID 4164) is:
 cϕ / cθ = a33
     *)
  Abort.

End CASE3.

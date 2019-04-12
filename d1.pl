% Test message
t(A) :- write(A), write("\n"), !. 

/* 3 DOF Helicopter Dynamics 
********************/

heli_dyn_model(ManipKinParams,ManipMassCenters,ManipMassParams) :- parameters([ManipKinParams,ManipMassCenters,ManipMassParams],P), var_parameters(P,VP), pure_symbols(VP,Variables), heli_dynamics(ManipKinParams,ManipMassCenters,ManipMassParams,Variables,F), decompose_fv(F,Variables,M,V,G), [0,0,0]=Z, BasePose=[Z,Z], multi_manipulators_jacobian(BasePose,ManipKinParams,Variables,J), transpose(J,T), write_intro(2), append([c(lm),c(kr),c(kl),v(ur),v(ul)],P,P1), write_parameters(P1), write("%% MODEL (do not edit):\n\n"), write_matrix(T,jt), write_matrix(M,m), write_vector(V,v), write_vector(G,g), write("fr = kr*ur;\nfl = kl*ul;\nft = fr+fl;\ntt = (fr-fl)*lm;\n f = [ft;tt];\n\n").

heli_dynamics(ManipKinParams,ManipMassCenters,ManipMassParams,Variables,F) :- [0,0,0]=Z, BasePose=[Z,Z], BaseMassCenter=Z, BaseMassParams=[0,Z], robot_potential_energy(BasePose,BaseMassCenter,BaseMassParams,ManipKinParams,ManipMassCenters,ManipMassParams,U), ManipKinParams=[LinksKinParams], ManipMassCenters=[MC], ManipMassParams=[MP], heli_kinetic_energy(BasePose,LinksKinParams,MC,MP,K), simp(sum([[K,1],[U,-1]]),L), dynamics(L,Variables,F).

heli_kinetic_energy(BasePose,LinksKinParams,MassCentersCoord,MassParams,E) :- heli_kinetic_energy(BasePose,LinksKinParams,MassCentersCoord,MassParams,0,E).
heli_kinetic_energy(BasePose,LinksKinParams,[CC|MassCentersCoord],[MP|MassParams],Temp,E) :- com_pose(BasePose,LinksKinParams,CC,P), select_last(LinksKinParams,LinksKinParams1), last(KinParams,LinksKinParams), var_parameters(KinParams,[V]), heli_part_kinetic_energy(P,V,MP,EB), simp(sum([[Temp,1],[EB,1]]),Temp1), heli_kinetic_energy(BasePose,LinksKinParams1,MassCentersCoord,MassParams,Temp1,E), !. 
heli_kinetic_energy(_,[],[],[],E,E).

heli_part_kinetic_energy(HomogeneousTransform,Variable,MP,K) :- MP=[Mass,[_,_,InertMom]], linear_velocity(HomogeneousTransform,LV), inner_product(LV,LV,LVS), simp(prod([[LVS,1],[Mass,1]]),LT), deriv(Variable,time,DV), simp(prod([[DV,2],[InertMom,1]]),AT), simp(sum([[LT,0.5],[AT,0.5]]),K). % kinetic energy of a single body

/* Constants
********************/

gravity_constant(c(gc)).

gravity_vector([0,G,0]) :- gravity_constant(G).

/* Forces Decomposition
********************/

decompose_fv(Forces,Variables,M,V,G) :- decompose_fv(Forces,Variables,[],[],[],M,V,G), !. % forces vector
decompose_fv([F|Fs],Variables,TempM,TempV,TempG,M,V,G) :- decompose(F,Variables,MR,VE,GE), append(TempM,[MR],TempM1), append(TempV,[VE],TempV1), append(TempG,[GE],TempG1), decompose_fv(Fs,Variables,TempM1,TempV1,TempG1,M,V,G), !. % aux 
decompose_fv([],_,M,V,G,M,V,G).

decompose(Force,Variables,M,V,G) :- Force=sum(F), decompose(F,Variables,[],F2,M), decompose(F2,Variables,0,0,V,G), !. % one force

decompose(F,[V|Vs],Temp,F2,M) :- decompose(F,V,0,F1,M1), append(Temp,[M1],Temp1), decompose(F1,Vs,Temp1,F2,M), !. % mass matrix
decompose(F,Variable,Temp,F2,M) :- atomic(Variable), insert_ddot(Variable,VD), member([prod(P),N],F), gms_member(VD,P,NV), select([prod(P),N],F,F1), select_from_gms(VD,NV,P,P1), simp(sum([[Temp,1],[prod(P1),N]]),Temp1), decompose(F1,Variable,Temp1,F2,M), !.
decompose(F,Variable,M,F,M) :- atomic(Variable), insert_ddot(Variable,VD), member([prod(P),_],F), gms_non_member(VD,P), !.
decompose(F,[],M,F,M) :- !.

decompose([F|Fs],Variables,TempV,TempG,N,G) :- F=[prod(P),_], member(V1,Variables), insert_dot(V1,VD1), gms_member(VD1,P,1), member(V2,Variables), insert_dot(V2,VD2), gms_member(VD2,P,1), simp(sum([[TempV,1],F]),TempV1), decompose(Fs,Variables,TempV1,TempG,N,G), !. % Coriolis force
decompose([F|Fs],Variables,TempV,TempG,N,G) :- F=[prod(P),_], member(V,Variables), insert_dot(V,VD), gms_member(VD,P,2), simp(sum([[TempV,1],F]),TempV1), decompose(Fs,Variables,TempV1,TempG,N,G), !. % centrifugal force
decompose([F|Fs],Variables,TempV,TempG,N,G) :- F=[prod(P),_], gravity_constant(GC), gms_member(GC,P,_), simp(sum([[TempG,1],F]),TempG1), decompose(Fs,Variables,TempV,TempG1,N,G), !. % gravity term
decompose([],_,V,G,V,G) :- !.

/* Velocities Decomposition
********************/

decompose(V,Variable,Derivative) :- decompose(V,Variable,0,Derivative), !.
decompose([V|Vs],U,Temp,D) :- V=[prod(P),M], insert_dot(U,UD), gms_member(UD,P,1), select_from_gms(UD,1,P,P1), simp(sum([[Temp,1],[prod(P1),M]]),Temp1), decompose(Vs,U,Temp1,D), !.
decompose([V|Vs],U,Temp,D) :- V=[prod(P),_], insert_dot(U,UD), gms_non_member(UD,P), decompose(Vs,U,Temp,D), !.
decompose([V|Vs],U,Temp,D) :- V=[v(dot(U)),1], simp(sum([[Temp,1],[1,1]]),Temp1), decompose(Vs,U,Temp1,D), !.
decompose([V|Vs],U,Temp,D) :- V=[v(X),1], X\=dot(U), decompose(Vs,U,Temp,D), !.
decompose([],_,D,D) :- !.

decompose_v(Velocity,Variables,JacobianRow) :- Velocity=0, length(Variables,N), zero_vector(JacobianRow,N), !.
decompose_v(Velocity,Variables,JacobianRow) :- Velocity=sum(V), decompose_v(V,Variables,[],JacobianRow), !.
decompose_v(Velocity,Variables,JacobianRow) :- Velocity=prod(V), decompose_v([[prod(V),1]],Variables,[],JacobianRow), !.
decompose_v(V,[U|Us],Temp,J) :- decompose(V,U,J1), append(Temp,[J1],Temp1), decompose_v(V,Us,Temp1,J), !. 
decompose_v(_,[],J,J) :- !.

decompose_vv(Velocities,Variables,Jacobian) :- decompose_vv(Velocities,Variables,[],Jacobian), !. % velocities vector
decompose_vv([V|Vs],U,Temp,J) :- decompose_v(V,U,JR), append(Temp,[JR],Temp1), decompose_vv(Vs,U,Temp1,J), !.
decompose_vv([],_,J,J).

/* Robot Dynamics
********************/

robot_dynamics_model(BasePose,BaseMassCenter,BaseMassParams,ManipKinParams,ManipMassCenters,ManipMassParams) :- parameters([BasePose,BaseMassCenter,BaseMassParams,ManipKinParams,ManipMassCenters,ManipMassParams],P), var_parameters(P,VP), pure_symbols(VP,Variables), robot_dynamics(BasePose,BaseMassCenter,BaseMassParams,ManipKinParams,ManipMassCenters,ManipMassParams,Variables,F), decompose_fv(F,Variables,M,V,G), multi_manipulators_jacobian(BasePose,ManipKinParams,Variables,J), transpose(J,T), write_intro(1), write_parameters(P), write("%% MODEL (do not edit):\n\n"), write_matrix(T,jt), write_matrix(M,m), write_vector(V,v), write_vector(G,g).

robot_dynamics(BasePose,BaseMassCenter,BaseMassParams,ManipKinParams,ManipMassCenters,ManipMassParams,Variables,F) :- robot_potential_energy(BasePose,BaseMassCenter,BaseMassParams,ManipKinParams,ManipMassCenters,ManipMassParams,U), robot_kinetic_energy(BasePose,BaseMassCenter,BaseMassParams,ManipKinParams,ManipMassCenters,ManipMassParams,K), simp(sum([[K,1],[U,-1]]),L), dynamics(L,Variables,F).

dynamics(Lagrangian,Variables,F) :- insert_dot(Variables,VariablesRates), gradient(Lagrangian,VariablesRates,DVR), deriv(DVR,time,T1), gradient(Lagrangian,Variables,T2), vec_sub(T1,T2,F).

robot_potential_energy(BasePose,BaseMassCenter,BaseMassParams,ManipKinParams,ManipMassCenters,ManipMassParams,E) :- BaseMassParams=[BaseMass,[_,_,_]], base_potential_energy(BasePose,BaseMassCenter,BaseMass,BE), multi_manipulators_potential_energy(BasePose,ManipKinParams,ManipMassCenters,ManipMassParams,ME), simp(sum([[BE,1],[ME,1]]),E). 

robot_kinetic_energy(BasePose,BaseMassCenter,BaseMassParams,ManipKinParams,ManipMassCenters,ManipMassParams,E) :- base_kinetic_energy(BasePose,BaseMassCenter,BaseMassParams,BE), multi_manipulators_kinetic_energy(BasePose,ManipKinParams,ManipMassCenters,ManipMassParams,ME), simp(sum([[BE,1],[ME,1]]),E). 

multi_manipulators_potential_energy(BasePose,ManipKinParams,ManipMassCenters,ManipMassParams,U) :- multi_manipulators_potential_energy(BasePose,ManipKinParams,ManipMassCenters,ManipMassParams,0,U).
multi_manipulators_potential_energy(BasePose,[KP|ManipKinParams],[MC|ManipMassCenters],[MP|ManipMassParams],Temp,U) :- manipulator_potential_energy(BasePose,KP,MC,MP,ME), simp(sum([[Temp,1],[ME,1]]),Temp1), multi_manipulators_potential_energy(BasePose,ManipKinParams,ManipMassCenters,ManipMassParams,Temp1,U), !.
multi_manipulators_potential_energy(_,[],[],[],U,U).

multi_manipulators_kinetic_energy(BasePose,ManipKinParams,ManipMassCenters,ManipMassParams,E) :- multi_manipulators_kinetic_energy(BasePose,ManipKinParams,ManipMassCenters,ManipMassParams,0,E).
multi_manipulators_kinetic_energy(BasePose,[KP|ManipKinParams],[MC|ManipMassCenters],[MP|ManipMassParams],Temp,E) :- manipulator_kinetic_energy(BasePose,KP,MC,MP,ME), simp(sum([[Temp,1],[ME,1]]),Temp1), multi_manipulators_kinetic_energy(BasePose,ManipKinParams,ManipMassCenters,ManipMassParams,Temp1,E), !.
multi_manipulators_kinetic_energy(_,[],[],[],E,E).

manipulator_potential_energy(BasePose,LinksKinParams,MassCentersCoord,MassParams,U) :- manipulator_potential_energy(BasePose,LinksKinParams,MassCentersCoord,MassParams,0,U).
manipulator_potential_energy(BasePose,LinksKinParams,[CC|MassCentersCoord],[MP|MassParams],Temp,U) :- MP=[Mass,[_,_,_]], com_pose(BasePose,LinksKinParams,CC,P), select_last(LinksKinParams,LinksKinParams1), potential_energy(P,Mass,EB), simp(sum([[Temp,1],[EB,1]]),Temp1), manipulator_potential_energy(BasePose,LinksKinParams1,MassCentersCoord,MassParams,Temp1,U).
manipulator_potential_energy(_,[],[],[],U,U).

manipulator_kinetic_energy(BasePose,LinksKinParams,MassCentersCoord,MassParams,E) :- manipulator_kinetic_energy(BasePose,LinksKinParams,MassCentersCoord,MassParams,0,E).
manipulator_kinetic_energy(BasePose,LinksKinParams,[CC|MassCentersCoord],[MP|MassParams],Temp,E) :- com_pose(BasePose,LinksKinParams,CC,P), select_last(LinksKinParams,LinksKinParams1), kinetic_energy(P,MP,EB), simp(sum([[Temp,1],[EB,1]]),Temp1), manipulator_kinetic_energy(BasePose,LinksKinParams1,MassCentersCoord,MassParams,Temp1,E), !. 
manipulator_kinetic_energy(_,[],[],[],E,E).

base_potential_energy(BasePose,BaseMassCenter,Mass,U) :- com_pose(BasePose,BaseMassCenter,P), potential_energy(P,Mass,U). 

base_kinetic_energy(BasePose,BaseMassCenter,BaseMassParams,E) :- com_pose(BasePose,BaseMassCenter,P), kinetic_energy(P,BaseMassParams,E). 

potential_energy(HomogeneousTransform,Mass,U) :- position(HomogeneousTransform,P), gravity_vector(G), inner_product(G,P,I), simp(prod([[Mass,1],[I,1]]),U).

kinetic_energy(HomogeneousTransform,MassParams,K) :- MassParams=[Mass,[InertMom1,InertMom2,InertMom3]], linear_velocity(HomogeneousTransform,LV), inner_product(LV,LV,LVS), simp(prod([[LVS,1],[Mass,1]]),LT), get_rotation_matrix(HomogeneousTransform,R), transpose(R,T), angular_velocity(HomogeneousTransform,AV), matrix_vector_product(T,AV,AVJ), AVJ=[AV1,AV2,AV3], simp(prod([[AV1,2],[InertMom1,1]]),AT1), simp(prod([[AV2,2],[InertMom2,1]]),AT2), simp(prod([[AV3,2],[InertMom3,1]]),AT3), simp(sum([[AT1,1],[AT2,1],[AT3,1]]),AT), simp(sum([[LT,0.5],[AT,0.5]]),K). % kinetic energy of a single body

/* Manipulator Kinematics 
********************/

multi_manipulators_jacobian(BasePose,ManipKinParams,Variables,Jacobian) :- multi_manipulators_velocities(BasePose,ManipKinParams,V), decompose_vv(V,Variables,Jacobian). % Jacobian in the joint frame

multi_manipulators_velocities(BasePose,ManipKinParams,V) :- multi_manipulators_velocities(BasePose,ManipKinParams,[],V).
multi_manipulators_velocities(B,[M|Ms],Temp,V) :- joint_pose(B,M,P), velocities_in_joint_frame(P,VM), append(Temp,VM,Temp1), multi_manipulators_velocities(B,Ms,Temp1,V), !.
multi_manipulators_velocities(_,[],V,V).

velocities_in_joint_frame(HomogeneousTransform,V) :- angular_velocity(HomogeneousTransform,A), linear_velocity(HomogeneousTransform,L), get_rotation_matrix(HomogeneousTransform,R), transpose(R,T), matrix_vector_product(T,L,L1), matrix_vector_product(T,A,A1), append(L1,A1,V).

angular_velocity(HomogeneousTransform,Velocity) :- get_rotation_matrix(HomogeneousTransform,R), deriv(R,time,DR), transpose(R,RT), get_row(DR,3,R1), get_column(RT,2,C1), get_row(DR,1,R2), get_column(RT,3,C2), get_row(DR,2,R3), get_column(RT,1,C3), inner_product(R1,C1,V1), inner_product(R2,C2,V2), inner_product(R3,C3,V3), Velocity=[V1,V2,V3].

linear_velocity(HomogeneousTransform,Velocity) :- position(HomogeneousTransform,[X,Y,Z]), deriv(X,time,DX), deriv(Y,time,DY), deriv(Z,time,DZ), Velocity=[DX,DY,DZ].

get_rotation_matrix(HomogeneousTransform,R) :- select_last(HomogeneousTransform,M), remove_last_column(M,R).

position(HomogeneousTransform,Posit) :- get_column(HomogeneousTransform,4,C), select_last(C,Posit).

com_pose(BasePose,LinksKinParams,MassCenterCoord,Pose) :- joint_pose(BasePose,LinksKinParams,JP), com_pose(MassCenterCoord,CP), matrix_product(JP,CP,Pose). % pose of a joint center of mass frame
com_pose(BasePose,MassCenterCoord,Pose) :- base_pose_transform(BasePose,P), com_pose(MassCenterCoord,MC), matrix_product(P,MC,Pose). % pose of the base center of mass frame
com_pose(MassCenterCoord,P) :- identity_3(I), homogeneous_transform(I,MassCenterCoord,P). % pose of the joint center of mass frame relative to the joint frame

joint_pose(LinkKinParams,P) :- LinkKinParams=[PrecTwist,PrecLength,Angle,Offset], rot_x(PrecTwist,RT), homogeneous_transform(RT,[PrecLength,0,0],S1), rot_z(Angle,RA), homogeneous_transform(RA,[0,0,Offset],S2), matrix_product(S1,S2,P), !. % homogenous transform representing joint pose relative to the previous joint
joint_pose(LinksKinParams,P) :- joint_pose(LinksKinParams,[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],P), !. % homogeneous transform representing joint pose relative to the base
joint_pose([LP|LinksKinParams],Temp,P) :- joint_pose(LP,JP), matrix_product(Temp,JP,Temp1), joint_pose(LinksKinParams,Temp1,P), !.
joint_pose([],P,P) :- !.
joint_pose(BasePose,LinksKinParams,P) :- base_pose_transform(BasePose,BT), joint_pose(LinksKinParams,LT), matrix_product(BT,LT,P). % joint pose relative to an inertial frame

base_pose_transform(BasePose,T) :- BasePose=[Posit,Orient], rot(Orient,R), homogeneous_transform(R,Posit,T). % homogeneous transform representing base pose

homogeneous_transform(RotMatrix,TransVec,T) :- append_column(RotMatrix,TransVec,T1), append(T1,[[0,0,0,1]],T).

rot(Orient,R) :- Orient=[Roll,Pitch,Yaw], rot_y(Pitch,R2), rot_z(Yaw,R3), matrix_product(R3,R2,P1), rot_x(Roll,R1), matrix_product(P1,R1,R). % transform representing rotation by roll, pitch and yaw

rot_x(Angle,R) :- R=[[1,0,0],[0,cos(Angle),sum([[sin(Angle),-1]])],[0,sin(Angle),cos(Angle)]].

rot_y(Angle,R) :- R=[[cos(Angle),0,sin(Angle)],[0,1,0],[sum([[sin(Angle),-1]]),0,cos(Angle)]].

rot_z(Angle,R) :- R=[[cos(Angle),sum([[sin(Angle),-1]]),0],[sin(Angle),cos(Angle),0],[0,0,1]].

/* Results Storage
********************/

write_parameters(P) :- write("%% PARAMETERS (need to be specified):\n\n% Constant parameters:\n"), gravity_constant(GC), rewrite_m(GC,GCT), write(GCT), write(" = 9.81;\n"), const_parameters(P,C), write_p(C), write("% Variable parameters (need to be measured or estimated):\n"), var_parameters(P,V), insert_dot(V,DV), append(V,DV,VD), write_p(VD).

write_p([P|Ps]) :- rewrite_m(P,T), write(T), write(" = 1;\n"), write_p(Ps), !.
write_p([]) :- write("\n").

write_intro(1) :- write("%% SERIAL MECHANISMS DYNAMICS MODEL\n\n% The model has form:\n% m*ddt + v + g = jt*f, where:\n% m - mass matrix,\n% ddt - second derivative of joint angles/offsets vector,\n% v - vector of Coriolis and centrifugal forces,\n% g - gravity terms vector,\n% jt - transposed Jacobian,\n% f - forces and moments acting on the end of mechanism.\n\n"), !.
write_intro(2) :- write("%% 3 DOF HELICOPTER DYNAMICS MODEL\n\n% The model has form:\n% m*ddt + v + g = jt*f, where:\n% m - mass matrix,\n% ddt - second derivative of joint angles vector,\n% v - vector of Coriolis and centrifugal forces,\n% g - gravity terms vector,\n% jt - transposed Jacobian,\n% f = [ft;tt],\n% ft = fr+fl,\n% tt = (fr-fl)*lm,\n% fr,fl - thrust force from the right and left motors, respectively,\n% lm - half of the distance between the motors.\n\n"), !.

/* Robot Parameters Analysis
********************/

parameters(L,P) :- flatten(L,P1), numbers_set(P1,_,P2), no_doubles(P2,P).

const_atom(N) :- N=c(X), atomic(X). 

var_atom(N) :- N=v(X), atomic(X). 

const_parameters(P,C) :- const_parameters(P,[],C).
const_parameters([P|Ps],T,C) :- const_atom(P), append(T,[P],T1), const_parameters(Ps,T1,C), !.
const_parameters([P|Ps],T,C) :- not(const_atom(P)), const_parameters(Ps,T,C), !.
const_parameters([],C,C).

var_parameters(P,V) :- var_parameters(P,[],V).
var_parameters([P|Ps],T,V) :- var_atom(P), append(T,[P],T1), var_parameters(Ps,T1,V), !.
var_parameters([P|Ps],T,V) :- not(var_atom(P)), var_parameters(Ps,T,V), !.
var_parameters([],V,V).

pure_symbols(L,P) :- pure_symbols(L,[],P).
pure_symbols([L|Ls],T,P) :- L=c(X), append(T,[X],T1), pure_symbols(Ls,T1,P), !.
pure_symbols([L|Ls],T,P) :- L=v(X), append(T,[X],T1), pure_symbols(Ls,T1,P), !.
pure_symbols([L|Ls],T,P) :- atomic(L), append(T,[L],T1), pure_symbols(Ls,T1,P), !.
pure_symbols([],P,P).

# construct nonsolvable groups of given order
# modified from perfect group construction
# Usage:
# ConstructNonsolvable(order);
# ConstructNonsolvable(order:from:=[[factorgrouporders],[indexpositions]]); for partial


#Limit for TransformingPermutationsCharacterTables (class number) in
#identifying factor groups
TPCTLIMIT:=200;

# seed is list of orders
MakeNonsolvableGroupOrders:=function(seed)
local from, upto,it,sim,i,a,ord,pp,j;
  seed:=Filtered(seed,x->x>1);
  from:=Minimum(seed);
  upto:=Maximum(seed);
  it:=SimpleGroupsIterator(1,upto);
  sim:=[];
  for i in it do
    a:=Size(i);
    AddSet(sim,Size(i));
  od;

  ord:=Filtered([from..upto],x->ForAny(sim,y->x mod y=0));

  return ord;
end;

# functions that could be used as isomorphism distinguishers
GpFingerprint:=function(g)
  if Size(g)<2000 and Size(g)<>512 and Size(g)<>1024 and Size(g)<>1536 then
    return IdGroup(g);
  else
    return [Size(g),IsPerfect(g),Collected(List(ConjugacyClasses(g),
      x->[Order(Representative(x)),Size(x)]))];
  fi;
end;

FPMaxReps:=function(g,a,b)
local l,s;
  l:=LowLayerSubgroups(g,a);
  s:=Set(List(l,Size));
  RemoveSet(s,Size(g));
  s:=Reversed(s);
  if b>Length(s) then return [];fi;
  return Filtered(l,x->Size(x)=s[b]);
end;

FINGERPRINTPROPERTIES:=[
  g->Collected(List(ConjugacyClasses(g),x->[Order(Representative(x)),Size(x)])),
  g->Collected(List(ConjugacyClasses(g),x->[Order(Representative(x)),GpFingerprint(Centralizer(x))])),
  g->Collected(List(MaximalSubgroupClassReps(g),GpFingerprint)),
  g->Collected(List(NormalSubgroups(g),x->[GpFingerprint(x),GpFingerprint(Centralizer(g,x))])),
  g->Collected(List(LowLayerSubgroups(g,2),GpFingerprint)),

  g->Size(AutomorphismGroup(g)),
  g->Collected(List(CharacteristicSubgroups(g),x->[GpFingerprint(x),GpFingerprint(Centralizer(g,x))])),
  #g->Collected(Flat(Irr(CharacterTable(g)))),
];

CHEAPFINGERPRINTLIMIT:=4;  # the first 4 fingerprint tests are cheap-ish

GrplistIds:=function(l)
local props,pool,test,c,f,r,tablecache,tmp,cheaplim;
  test:=function(p)
  local a,new,sel,i,dup,tmp;
    if c=Length(l) then return;fi;# not needed
    dup:=List(Filtered(Collected(pool),x->x[2]>1),x->x[1]);
    sel:=Filtered([1..Length(l)],x->pool[x] in dup);
    a:=[];
    for i in sel do
      tmp:=Group(GeneratorsOfGroup(l[i]));
      SetSize(tmp,Size(l[i]));
      a[i]:=p(tmp);
    od;
    if ForAny(dup,x->Length(Set(a{Filtered(sel,y->pool[y]=x)}))>1) then
      for i in sel do Add(pool[i],a[i]); od;
      Add(props,p);
      c:=Length(Set(pool));
    fi;
  end;

  props:=[];
  pool:=List(l,x->[]);c:=1;
  for f in FINGERPRINTPROPERTIES do test(f);od;
  cheaplim:=PositionProperty(List(props,x->Position(FINGERPRINTPROPERTIES,x)),
    x->x>CHEAPFINGERPRINTLIMIT);
  if cheaplim=fail then cheaplim:=Length(props);
  else cheaplim:=cheaplim-1;fi;

  if c<Length(l) then
    tablecache:=[];
    Print("will have to rely on isomorphism tests\n");
  fi;

  r:=rec(props:=props,pool:=pool,
    groupinfo:=List(l,x->[Size(x),GeneratorsOfGroup(x)]),
    isomneed:=Filtered([1..Length(pool)],x->Number(pool,y->y=pool[x])>1),

    idfunc:=function(arg)
      local gorig,a,f,p,g,fingerprints,cands,badset,goodset,i,cheap,rprop;
        gorig:=arg[1];
        if Length(arg)>1 then
          badset:=arg[2];
          goodset:=arg[3];
        else
          badset:=[];
          goodset:=[];
        fi;
        cheap:=arg[Length(arg)]=true; #do cheap test only?

        if Length(r.pool)=1 then return 1;fi;
        g:=gorig;

        if IsBound(g!.fingerprints) then
          fingerprints:=g!.fingerprints;
        else
          fingerprints:=[];
          g!.fingerprints:=fingerprints;
        fi;
        if IsPermGroup(g) then
          if IsSolvableGroup(g) then
            g:=Image(IsomorphismPcGroup(g));
          else
            g:=Image(SmallerDegreePermutationRepresentation(g));
          fi;
          a:=Size(g);
          g:=Group(GeneratorsOfGroup(g)); # avoid caching lots of data
          SetSize(g,a);
        fi;
        a:=[];
        if cheap then rprop:=r.props{[1..cheaplim]};
        else rprop:=r.props;fi;
        for f in rprop do
          p:=PositionProperty(fingerprints,x->x[1]=f);
          if p=fail then
            Add(a,f(g));
            Add(fingerprints,[f,a[Length(a)]]);
          else
            Add(a,fingerprints[p][2]);
          fi;
          cands:=Filtered([1..Length(r.pool)],x->
            Length(r.pool[x])>=Length(a) and r.pool[x]{[1..Length(a)]}=a);
          if IsSubset(badset,cands) then
            Print("badcand ",cands,"\n");
            return "bad";
          fi;
          if IsSubset(goodset,cands) then
            Print("goodcand ",cands,"\n");
            return "good";
          fi;
          if Length(cands)>1 then Print("Cands=",cands,"\n");fi;

          p:=Position(r.pool,a);
          if IsInt(p) and not p in r.isomneed then
            Print("exact:",p,"\n");
            return p;
          fi;
        od;
        if cheap then
          a:=Filtered([1..Length(r.pool)],
            x->r.pool[x]{[1..Minimum(cheaplim,Length(r.pool[x]))]}=a);
          Print("cheap:",a,"\n");
          return a;
        fi;

        a:=Filtered([1..Length(r.pool)],x->r.pool[x]=a);

	if Length(ConjugacyClasses(g))<=TPCTLIMIT then
	  f:=Length(a);
	  for i in ShallowCopy(a) do
	    if Length(a)>1 then
	      if not IsBound(tablecache[i]) then
		tmp:=Group(r.groupinfo[i][2]);
		SetSize(tmp,r.groupinfo[i][1]);
		tmp:=ShallowCopy(CharacterTable(tmp));
                Size(tmp);
                Irr(tmp);
                Unbind(tmp!.ConjugacyClasses); # avoid caching groups
                Unbind(tmp!.UnderlyingGroup);
		tablecache[i]:=tmp;
	      fi;
	      if TransformingPermutationsCharacterTablesTimeout(
                 CharacterTable(g),tablecache[i],
                 QuoInt(Size(g),5000))=fail then
		RemoveSet(a,i);
	      fi;
	    fi;
	  od;
	  if Length(a)<f then
	    Print("Character table test reduces ",f,"->", Length(a),"\n");
	  fi;
	fi;

	while Length(a)>1 do
	  i:=a[1];
	  a:=a{[2..Length(a)]};
          tmp:=Group(r.groupinfo[i][2]);
          SetSize(tmp,r.groupinfo[i][1]);
	  if IsomorphismGroups(g,tmp)<>fail then
            Print("isomtest:",i,"\n");
	    return i;
	  fi;
	od;
        Print("table:",a[1],"\n");
	return a[1];
      end);
  l:=false; # clean memory
  return r;
end;

#IdGrplist:=function(r,g)
#  return r.idfunc(g);
#end;

# Format of entries: [Order,Grouplist]
if not IsBound(PERFECTLIST) then
  PERFECTLIST:=[];
fi;

MemoryEfficientVersion:=function(G)
local piso,f,k,pf,new;
  piso:=IsomorphismPermGroup(G);
  f:=FreeGroup(List(GeneratorsOfGroup(FreeGroupOfFpGroup(G)),String));
  new:=f/List(RelatorsOfFpGroup(G),x->MappedWord(x,FreeGeneratorsOfFpGroup(G),
    GeneratorsOfGroup(f)));
  k:=List(SMALLGENERATINGSETGENERIC(Image(piso)),
    x->PreImagesRepresentative(piso,x));
  pf:=List(k,x->ImagesRepresentative(piso,x));
  k:=List(k,x->ElementOfFpGroup(FamilyObj(One(new)),MappedWord(
    UnderlyingElement(x),FreeGeneratorsOfFpGroup(G),GeneratorsOfGroup(f))));
  #pf:=MappingGeneratorsImages(piso)[2];
  pf:=GroupHomomorphismByImagesNC(new,Group(pf),k,pf);
  SetIsomorphismPermGroup(new,pf);
  return new;
end;

MyIsomTest:=function(g,h)
local c,d,f;
  for f in FINGERPRINTPROPERTIES do
    if f(g)<>f(h) then return false;fi;
  od;
  if Length(ConjugacyClasses(g))<500 then
    c:=CharacterTable(g);;Irr(c);
    d:=CharacterTable(h);;Irr(d);
    if TransformingPermutationsCharacterTablesTimeout(c,d,
      QuoInt(Size(g),5000))=fail then return false; fi;
  fi;

  c:=Size(g);
  if Length(GeneratorsOfGroup(g))>5 then
    g:=Group(SmallGeneratingSet(g));
    SetSize(g,c);
  fi;
  if Length(GeneratorsOfGroup(h))>5 then
    h:=Group(SmallGeneratingSet(h));
    SetSize(h,c);
  fi;
  return IsomorphismGroups(g,h)<>fail;
end;

FittingFreeGroupsSocle:=function(soc)
local A,iso,G,s,nat,u,sub,i,j,h,l,fp;
  A:=AutomorphismGroup(soc);
  iso:=IsomorphismPermGroup(A);
  G:=Image(iso);
  s:=Socle(G);
  if Size(s)<>Size(soc) then
    Error("socle changed");
  fi;
  nat:=NaturalHomomorphismByNormalSubgroup(G,s);
  u:=List(ConjugacyClassesSubgroups(Image(nat,G)),Representative);

  sub:=[];
  for i in u do
    h:=PreImage(nat,i);
    if Size(RadicalGroup(h))=1 then
      l:=Filtered(sub,x->Size(x)=Size(h));
      for j in [1..Length(FINGERPRINTPROPERTIES)] do
        if Length(l)>0 then
          #Print("Property ",j,"\n");
          fp:=FINGERPRINTPROPERTIES[j](h);
          l:=Filtered(l,x->FINGERPRINTPROPERTIES[j](x)=fp);
        fi;
      od;
      l:=Filtered(l,x->IsomorphismGroups(x,h)<>fail);
      if Length(l)=0 then Add(sub,h);fi;
    fi;
  od;
  return sub;
end;

# split out as that might help with memory
DoNonsolvableConstructionFor:=function(q,j,nts,ids)
local respp,cf,m,mpos,coh,fgens,comp,reps,v,new,isok,pema,pf,gens,nt,quot,
      res,qk,p,e,k,primax,au,oldqk;

  primax:=NrPerfectGroups(Size(q));
  if primax=fail and ForAny(PERFECTLIST,x->x[1]=Size(q)) then
    primax:=First(PERFECTLIST,x->x[1]=Size(q));
    if primax=fail then Error("list missing");fi;
    primax:=primax[2];
  fi;
  p:=Factors(nts)[1];
  e:=LogInt(nts,p);
  res:=[];
  respp:=[];

  # is there a chance for modules -- which factors would fit into GL
  quot:=Size(GL(e,p));
  cf:=Filtered(NormalSubgroups(q),x->IndexNC(q,x)>1
    and (quot mod IndexNC(q,x)=0));
  if Length(cf)=0 then cf:=q;
  else cf:=Intersection(cf);fi;

  if Size(cf)=1 then
    new:=IdentityMapping(q);
    cf:=IrreducibleModules(q,GF(p),e);
    if cf[1]<>GeneratorsOfGroup(q) then Error("gens1");fi;
  elif Size(cf)=Size(q) then
    Print("Dimension is too small for nontrivial factors\n");
    cf:=[GeneratorsOfGroup(q),[TrivialModule(Length(GeneratorsOfGroup(q)),GF(p))]];
  else
    new:=NaturalHomomorphismByNormalSubgroup(q,cf);
    Print("Reduced module question to factor of order ",Size(Range(new)),"\n");
    fgens:=List(GeneratorsOfGroup(q),x->ImagesRepresentative(new,x));
    cf:=IrreducibleModules(GroupWithGenerators(fgens),GF(p),e);
    if cf[1]<>fgens then
      # translate generators
      new:=[];
      for k in cf[2] do
        pema:=GroupHomomorphismByImages(Group(fgens),Group(k.generators),cf[1],k.generators);
        Add(new,GModuleByMats(List(fgens,x->ImagesRepresentative(pema,x)),k.field));
      od;
      cf:=[fgens,new];
    fi;
    cf:=[GeneratorsOfGroup(q),cf[2]];
  fi;

  cf:=Filtered(cf[2],x->x.dimension=e);
  List(cf,MTX.IsIrreducible);

  if Length(cf)>1 then
    Print("Test for isomorphic modules\n");
    # eliminate images under automorphisms
    pema:=AutomorphismGroup(q);
    comp:=[];
    new:=[];
    for m in cf do
      if not ForAny(comp,x->MTX.Isomorphism(m,x)<>fail) then
        Add(comp,m);
        Add(new,m);
        # autom orbit
        k:=Length(comp);
        while k<=Length(comp) do
          qk:=GroupHomomorphismByImages(q,Group(comp[k].generators),GeneratorsOfGroup(q),
            comp[k].generators);
          for au in GeneratorsOfGroup(pema) do
            reps:=List(GeneratorsOfGroup(q),
              x->ImagesRepresentative(qk,ImagesRepresentative(au,x)));
            reps:=GModuleByMats(reps,GF(p));
            MTX.IsIrreducible(reps);
            if not ForAny(comp,x->MTX.Isomorphism(reps,x)<>fail) then
              Add(comp,reps);
            fi;
          od;
          k:=k+1;
        od;
      fi;
    od;

    if new<>cf then
      Print("Reduce ",Length(cf)," to ",Length(new)," modules\n");
      cf:=new;
    fi;
  fi;

  for m in cf do
    mpos:=Position(cf,m);
    Print("Module dimension ",m.dimension,"\n");
    coh:=TwoCohomologyGeneric(q,m);
    fgens:=GeneratorsOfGroup(coh.presentation.group);

    comp:=[];
    if Length(coh.cohomology)=0 then
      reps:=[coh.zero];
    elif Length(coh.cohomology)=1 and p=2 then
      reps:=[coh.zero,coh.cohomology[1]];
    else
      comp:=CompatiblePairs(q,m);
      reps:=CompatiblePairOrbitRepsGeneric(comp,coh);
    fi;
    Print("Compatible pairs ",Size(comp)," give ",Length(reps),
          " orbits from ",Length(coh.cohomology),"\n");
    for v in reps do
      new:=FpGroupCocycle(coh,v,true);
      isok:=true;

      if isok then
        # could it have been gotten in another way?
        pema:=IsomorphismPermGroup(new);
        pema:=pema*SmallerDegreePermutationRepresentation(Image(pema));
        pf:=Image(pema);

        # generators that give module action
        gens:=List(coh.presentation.prewords,
          x->MappedWord(x,fgens,GeneratorsOfGroup(pf){[1..Length(fgens)]}));
        # want: generated through smallest normal subgroup, first
        # module of this kind for factor, first factor group
        #nt:=Filtered(NormalSubgroups(pf),IsElementaryAbelian);
        nt:=Filtered(MinimalNormalSubgroups(pf),x->IsPrimePowerInt(Size(x)));
        if ForAll(nt,x->Size(x)>=nts) then
          nt:=Filtered(nt,x->Size(x)=nts);

          # leave out the one how it was created
          quot:=GroupHomomorphismByImagesNC(pf,coh.group,
            List(GeneratorsOfGroup(new),x->ImagesRepresentative(pema,x)),
              Concatenation(
              List(GeneratorsOfGroup(Range(coh.fphom)),
                x->PreImagesRepresentative(coh.fphom,x)),
                ListWithIdenticalEntries(coh.module.dimension,
                  One(coh.group))
                ));
          qk:=KernelOfMultiplicativeGeneralMapping(quot);
          nt:=Filtered(nt,x->x<>qk);

          # consider the factor groups:
          # any smaller index -> discard
          # any equal index -> test
          # otherwise accept

          # first do all with cheap test only (to find bad)
          k:=1;
          oldqk:=[];
          while isok<>false and k<=Length(nt) do
            qk:=ids.idfunc(pf/nt[k],[1..j-1],[j+1..primax],
              true); # cheap test
            oldqk[k]:=qk;
            if (IsInt(qk) and qk<j) or qk="bad" then isok:=false;fi;
            k:=k+1;
          od;

          if isok=false then
            Print("quickdecide\n");
          else
            k:=1;
            while isok<>false and k<=Length(nt) do
              qk:=oldqk[k];
              if IsList(qk) and ForAny(qk,IsInt) then
                # try to do better
                Print("try harder for ",qk,"\n");
                qk:=ids.idfunc(pf/nt[k],[1..j-1],[j+1..primax]);
#if qk<>oldqk[k] then Error("UGH",qk,oldqk[k]);
              fi;
              if (IsInt(qk) and qk<j) or qk="bad" then isok:=false;
              elif IsInt(qk) and qk=j then isok:=fail;fi;
              k:=k+1;
            od;
          fi;

          if (isok=fail and Length(respp)>0) then
            Print("Need ",Length(respp)," isomorphism tests\n");
elif (isok=true and Length(respp)>0) then
  Print("Avoid ",Length(respp)," isomorphism tests\n");
          fi;

          if (isok=true or (isok=fail and ForAll(respp,x->MyIsomTest(x,pf)=false))) then
            Add(res,new);
            if isok=fail then
              Add(respp,pf); # local list of those that have multiple normals with this
              # factor type. Only these needed for isom test
            fi;
            Print("found nr. ",Length(res),"\n");
          else
            Print("smallerc\n");
          fi;

        else
          Print("smallera\n");
        fi;
      else
        Error("dead case\n");
      fi;
    od;

  od; #for m

  # cleanup of cached data to save memory
  for m in [1..Length(res)] do
    res[m]:=MemoryEfficientVersion(res[m]);
    res[m]!.builtfrom:=j;
  od;
  return res;
end;

# option from is list, entry 1 is orders, entry s2, if given, indices
ConstructNonsolvable:=function(n)
local globalres,resp,d,i,j,nt,p,e,q,cf,m,coh,v,new,quot,nts,pf,pl,comp,reps,
      ids,all,gens,fgens,mpos,ntm,dosubdir,isok,qk,k,respp,pema,from,ran,
      old;

  if n>=60^6 then Error("Cannot do yet");fi;
  from:=ValueOption("from");
  dosubdir:=false;

  globalres:=ValueOption("globalres");
  if globalres=fail then
    globalres:=[];
  else
    globalres:=ShallowCopy(globalres);
    Print("Got ",Length(globalres)," existing groups\n");
  fi;

  # fitting free groups from list
  ran:=Filtered(FFGROUPS,x->Size(x)=n);
  for i in ran do Add(globalres,i);od;

  #resp:=[];
  q:=POSSIBLE_ORDERS;
  d:=Filtered(DivisorsInt(n),x->x<n and x in q and IsPrimePowerInt(n/x));

  if from<>fail then d:=Intersection(d,from[1]);fi;

  for i in d do
    nts:=n/i;
    #if IsPrimePowerInt(nts) then   # always true
      pl:=[];
      #if NrNonsolvableGroups(i)=0 then
      #  all:=First(PERFECTLIST,x->x[1]=i)[2];
      #else
        all:=List([1..NrNonsolvableGroups(i)],x->NonsolvableGroup(i,x));
      #fi;
      ids:=GrplistIds(all);
      for j in [1..Length(all)] do
        q:=all[j];
        if HasName(q) then
          new:=Name(q);
        else
          new:=Concatenation("Nonsolv(",String(Size(q)),",",String(j),")");
        fi;
        q:=Group(SmallGeneratingSet(q));
        SetName(q,new);
        Add(pl,q);
      od;

      ran:=[1..Length(pl)];
      if from<>fail and Length(from)>1 and Length(from[1])=1 then
        ran:=from[2];
      fi;
      for j in ran do
        old:=Length(globalres);
        q:=pl[j];
        Print("Using ",i,", ",j," (of ",Length(ran),"): ",q,"\n");
        Append(globalres,DoNonsolvableConstructionFor(q,j,nts,ids));
        Print("Total now: ",Length(globalres)," groups\n");
        # kill factor group and associated info, as not needed any longer
        Unbind(pl[j]);

      od; # for j in ran
#    elif nts<=i then
#      #nts is not prime power, try to do direct products of simple
#      q:=SimpleGroupsIterator(nts,nts);
#      old:=[];
#      for j in q do Add(old,j);od;
#      if Length(old)>0 then
#        if NrPerfectLibraryGroups(i)=0 then
#          all:=First(PERFECTLIST,x->x[1]=i)[2];
#        else
#          all:=List([1..NrPerfectGroups(i)],x->PerfectGroup(IsPermGroup,i,x));
#        fi;
#        all:=Filtered(all,x->Size(RadicalGroup(x))=1 and
#          (IsSimple(x) or ForAll(MinimalNormalSubgroups(x),y->Size(y)<=nts))
#          );
#        if Length(all)>0 then
#          for j in Cartesian(old,all) do
#            Print("Direct Product:",j,"\n");
#            #j:=List(j,x->Image(IsomorphismFpGroup(x)));
#            Add(globalres,Image(IsomorphismFpGroup(DirectProduct(j[1],j[2]))));
#          od;
#        fi;
#      fi;
#    fi;
  od;
  return globalres;
end;

AllToPerm:=function(l)
local i,g,p,h;
  for i in [1..Length(l)] do
    g:=l[i];
    if not IsPermGroup(g) then
      g:=Image(IsomorphismPermGroup(g));
    fi;
    p:=NrMovedPoints(g);
    h:=SmallerDegreePermutationRepresentation(g);
    while NrMovedPoints(Range(h))<NrMovedPoints(g) do
      g:=Image(h,g);
      h:=SmallerDegreePermutationRepresentation(g);
    od;

    if Size(g)<10000 and NrMovedPoints(g)^2*2>Size(g) then
      g:=Image(MinimalFaithfulPermutationRepresentation(g),g);
    fi;
    Print("Group ",i,": ",p,"=>",NrMovedPoints(g),"\n");
    h:=Group(SmallestGeneratingSetHT(g));
    if h<>g then Error();fi;
    l[i]:=h;
  od;
  return l;
end;

StoreTempResult:=function(file,l)
local i,iso;
  PrintTo(file,"return [");
  for i in l do
    iso:=IsomorphismPermGroup(i);
    AppendTo(file,"[",i!.builtfrom,",",List(GeneratorsOfGroup(i),String),",\n",
      List(RelatorsOfFpGroup(i),LetterRepAssocWord),",\n",
      List(MappingGeneratorsImages(iso)[1],
         x->LetterRepAssocWord(UnderlyingElement(x))),",\n",
      MappingGeneratorsImages(iso)[2],"],\n");
  od;
  AppendTo(file,"];");
end;

LoadTempResult:=function(file)
local res,l,i,f,g,gens,rels;
  res:=[];
  l:=ReadAsFunction(file)();
  for i in l do
    f:=FreeGroup(i[2]);
    rels:=List(i[3],x->AssocWordByLetterRep(FamilyObj(One(f)),x));
    g:=f/rels;
    g!.builtfrom:=i[1];
    gens:=List(i[4],x->AssocWordByLetterRep(FamilyObj(One(f)),x));
    gens:=List(gens,x->ElementOfFpGroup(FamilyObj(One(g)),x));
    SetIsomorphismPermGroup(g,
      GroupHomomorphismByImagesNC(g,Group(i[5]),gens,i[5]));
    Add(res,g);
  od;
  return res;
end;

# Function to generate library file
PrintPerfectStorageData:=function(file,l)
local i,j,a,p,s,w,idx,sz,g,sim,sg,newf,newrels,new,per,o,rk,smallgenfp,gs,num,
  upd,tbl,stb,jl,jt,hast,jp;

  smallgenfp:=function(a)
  local sz,imgs,i,c;
    sz:=Size(a);
    imgs:=List(GeneratorsOfGroup(a),x->ImagesRepresentative(per,x));
    for i in [1..Length(imgs)] do
      for c in Combinations(imgs,i) do
        if Size(Group(c))=sz then
          return GeneratorsOfGroup(a){List(c,x->Position(imgs,x))};
        fi;
      od;
    od;
  end;

  sz:=Size(l[1]);

  w:=SizeScreen()[1];
  idx:=Position(PERFRec.sizes,sz);
  if idx=fail then idx:=2*Length(PERFRec.sizes);fi;
  a:=ShallowCopy(PERFRec.number);
  a[idx]:=Length(l);

  PrintTo(file,
"#############################################################################\n",
"##\n",
"##  This file is part of GAP, a system for computational discrete algebra.\n",
"##  It contains the perfect groups of order ",sz,"\n",
"##  This data was computed by Alexander Hulpke\n",
"##  It is distributed under the artistic license 2.0\n",
"##  https://opensource.org/licenses/Artistic-2.0\n\n");

  AppendTo(file,"number:=",a,";\n\n","PERFGRP[",idx,"]:=[");

  for i in [1..Length(l)] do
    sz:=Size(l[i]);
    Print("Doing ",i,"\n");
    if HasPerfectIdentification(l[i]) then
      num:=PerfectIdentification(l[i]);
      upd:=true;
    else
      num:=[sz,i];
      upd:=false;
    fi;
    if i>1 then AppendTo(file,",\n");fi;
    if upd then AppendTo(file,"# <<<< \n\n");fi;

    g:=l[i];
    if not IsFpGroup(g) then
      p:=IsomorphismFpGroup(g);
      g:=Range(p);
      SetSize(g,Size(Source(p)));
    fi;
    if not upd then
      sim:=IsomorphismSimplifiedFpGroup(g); # kill redundant stuff
      sg:=Range(sim);
      rk:=Length(GeneratorsOfGroup(sg));
      newf:=FreeGroup(List([1..Length(GeneratorsOfGroup(sg))],x->[CHARS_LALPHA[x]]));
      newrels:=List(RelatorsOfFpGroup(sg),
        x->MappedWord(x,FreeGeneratorsOfFpGroup(sg),GeneratorsOfGroup(newf)));
      new:=newf/newrels; SetSize(new,Size(g));

      per:=IsomorphismPermGroup(g);
      # reduce degree until kingdom come
      repeat
        p:=NrMovedPoints(Range(per));
        per:=per*SmallerDegreePermutationRepresentation(Image(per));
      until p=NrMovedPoints(Range(per));
      p:=Image(per);
      per:=GroupHomomorphismByImagesNC(new,p,GeneratorsOfGroup(new),
            List(GeneratorsOfGroup(sg),x->ImagesRepresentative(per,
              PreImagesRepresentative(sim,x))));
      SetIsomorphismPermGroup(new,per);
    else
      new:=g;
      newrels:=RelatorsOfFpGroup(g);
      rk:=Length(GeneratorsOfGroup(g));
      per:=IsomorphismPermGroup(g);
      p:=Image(per);
    fi;

    o:=Orbits(p,MovedPoints(p));
    stb:=List(o,x->Stabilizer(p,x[1]));
    s:=List(stb,x->PreImage(per,x));
    gs:=List(s,x->ShallowCopy(GeneratorsOfGroup(x))); # trigger gens

    AppendTo(file,"# ",num[1],".",num[2],"\n",
    "[[1,\"",CHARS_LALPHA{[1..rk]},"\",\nfunction(");
    for j in [1..rk] do
      if j>1 then AppendTo(file,",");fi;
      AppendTo(file,CHARS_LALPHA{[j]});
    od;
    AppendTo(file,")\nreturn [",newrels,",\n");

    a:=[];
    for jp in [1..Length(gs)] do
      j:=gs[jp];
      j:=List(j,UnderlyingElement);

      hast:=false;
      jl:=Length(j);
      tbl:=[];
      while jl>15 and IsList(tbl) do
        jt:=j{Union([1..10],List([1..QuoInt(jl,2)],x->Random([1..jl])))};
        tbl:=TCENUM.CosetTableFromGensAndRels(
          FreeGeneratorsOfFpGroup(new),RelatorsOfFpGroup(new),jt:quiet);
        if IsList(tbl) and Length(tbl[1])=Length(o[jp]) then
          Print("genreduce ",Length(jt),"\n");
          j:=jt;
          jl:=Length(j);
          hast:=true;
        fi;
      od;

      if not hast then
        # force that coset enum finishes
        tbl:=TCENUM.CosetTableFromGensAndRels(
          FreeGeneratorsOfFpGroup(new),RelatorsOfFpGroup(new),j);
        if not (IsList(tbl) and Length(tbl[1])=Length(o[jp])) then
          Error("cosetenum!");
        fi;
      fi;

      Add(a,j);
    od;

    if upd then AppendTo(file,"\n# >>>> \n");fi;
    AppendTo(file,a,"];\nend,\n",List(o,Length),"],\n\"PG",num[1],".",num[2],
      "\",", "0," # no hpNumber
    );
    a:=Centre(p);
    if IsSimpleGroup(p/a) then
      a:=-Size(a);
    else
      a:=Size(a);
    fi;
    AppendTo(file,a,",");
    # simple factors
    s:=CompositionSeries(p);
    a:=[];
    for j in [2..Length(s)] do
      if not HasAbelianFactorGroup(s[j-1],s[j]) then
        w:=Filtered([1..Length(PERFRec.sizeNumberSimpleGroup)],
          x->PERFRec.sizeNumberSimpleGroup[x][1]=IndexNC(s[j-1],s[j]));
        if Length(w)<>1 then Error(
          "size not unique -- Make sure `w[1]` is correct wirh `s[j-1]/s[j]`");
        fi;
        w:=w[1];
        Add(a,w);
      fi;
    od;
    if Length(a)=1 then a:=a[1];fi;

    AppendTo(file,a,",");
    a:=List(o,Length);
    if Length(a)=1 then a:=a[1];fi;
    AppendTo(file,a,"]");
  od;

  AppendTo(file,"];\n");
end;

POSSIBLE_ORDERS:=[ 60, 120, 168, 180, 240, 300, 336, 360, 420, 480, 504, 540, 600, 660, 672,
  720, 780, 840, 900, 960, 1008, 1020, 1080, 1092, 1140, 1176, 1200, 1260,
  1320, 1344, 1380, 1440, 1500, 1512, 1560, 1620, 1680, 1740, 1800, 1848,
  1860, 1920, 1980, 2016, 2040, 2100, 2160, 2184, 2220, 2280, 2340, 2352,
  2400, 2448, 2460, 2520, 2580, 2640, 2688, 2700, 2760, 2820, 2856, 2880,
  2940, 3000, 3024, 3060, 3120, 3180, 3192, 3240, 3276, 3300, 3360, 3420,
  3480, 3528, 3540, 3600, 3660, 3696, 3720, 3780, 3840, 3864, 3900, 3960,
  4020, 4032, 4080, 4140, 4200, 4260, 4320, 4368, 4380, 4440, 4500, 4536,
  4560, 4620, 4680, 4704, 4740, 4800, 4860, 4872, 4896, 4920, 4980, 5040,
  5100, 5160, 5208, 5220, 5280, 5340, 5376, 5400, 5460, 5520, 5544, 5580,
  5616, 5640, 5700, 5712, 5760, 5820, 5880, 5940, 6000, 6048, 6060, 6072,
  6120, 6180, 6216, 6240, 6300, 6360, 6384, 6420, 6480, 6540, 6552, 6600,
  6660, 6720, 6780, 6840, 6888, 6900, 6960, 7020, 7056, 7080, 7140, 7200,
  7224, 7260, 7320, 7344, 7380, 7392, 7440, 7500, 7560, 7620, 7644, 7680,
  7728, 7740, 7800, 7860, 7896, 7920, 7980, 8040, 8064, 8100, 8160, 8220,
  8232, 8280, 8340, 8400, 8460, 8520, 8568, 8580, 8640, 8700, 8736, 8760,
  8820, 8880, 8904, 8940, 9000, 9060, 9072, 9120, 9180, 9240, 9300, 9360,
  9408, 9420, 9480, 9540, 9576, 9600, 9660, 9720, 9744, 9780, 9792, 9828,
  9840, 9900, 9912, 9960, 10020, 10080, 10140, 10200, 10248, 10260, 10320,
  10380, 10416, 10440, 10500, 10560, 10584, 10620, 10680, 10740, 10752,
  10800, 10860, 10920, 10980, 11040, 11088, 11100, 11160, 11220, 11232,
  11256, 11280, 11340, 11400, 11424, 11460, 11520, 11580, 11592, 11640,
  11700, 11760, 11820, 11880, 11928, 11940, 12000, 12012, 12060, 12096,
  12120, 12144, 12180, 12240, 12264, 12300, 12360, 12420, 12432, 12480,
  12540, 12600, 12660, 12720, 12768, 12780, 12840, 12900, 12936, 12960,
  13020, 13080, 13104, 13140, 13200, 13260, 13272, 13320, 13380, 13440,
  13500, 13560, 13608, 13620, 13680, 13740, 13776, 13800, 13860, 13920,
  13944, 13980, 14040, 14100, 14112, 14160, 14196, 14220, 14280, 14340,
  14400, 14448, 14460, 14520, 14580, 14616, 14640, 14688, 14700, 14760,
  14784, 14820, 14880, 14940, 14952, 15000, 15060, 15120, 15180, 15240,
  15288, 15300, 15360, 15420, 15456, 15480, 15540, 15600, 15624, 15660,
  15720, 15780, 15792, 15840, 15900, 15960, 16020, 16080, 16128, 16140,
  16200, 16260, 16296, 16320, 16380, 16440, 16464, 16500, 16560, 16620,
  16632, 16680, 16740, 16800, 16848, 16860, 16920, 16968, 16980, 17040,
  17100, 17136, 17160, 17220, 17280, 17304, 17340, 17400, 17460, 17472,
  17520, 17580, 17640, 17700, 17760, 17808, 17820, 17880, 17940, 17976,
  18000, 18060, 18120, 18144, 18180, 18216, 18240, 18300, 18312, 18360,
  18420, 18480, 18540, 18564, 18600, 18648, 18660, 18720, 18780, 18816,
  18840, 18900, 18960, 18984, 19020, 19080, 19140, 19152, 19200, 19260,
  19320, 19380, 19440, 19488, 19500, 19560, 19584, 19620, 19656, 19680,
  19740, 19800, 19824, 19860, 19920, 19980, 19992, 20040, 20100, 20160,
  20220, 20280, 20328, 20340, 20400, 20460, 20496, 20520, 20580, 20640,
  20664, 20700, 20748, 20760, 20820, 20832, 20880, 20940, 21000, 21060,
  21120, 21168, 21180, 21240, 21300, 21336, 21360, 21420, 21480, 21504,
  21540, 21600, 21660, 21672, 21720, 21780, 21840, 21900, 21960, 22008,
  22020, 22032, 22080, 22140, 22176, 22200, 22260, 22320, 22344, 22380,
  22440, 22464, 22500, 22512, 22560, 22620, 22680, 22740, 22800, 22848,
  22860, 22920, 22932, 22980, 23016, 23040, 23100, 23160, 23184, 23220,
  23280, 23340, 23352, 23400, 23460, 23520, 23580, 23640, 23688, 23700,
  23760, 23820, 23856, 23880, 23940, 24000, 24024, 24060, 24120, 24180,
  24192, 24240, 24288, 24300, 24360, 24420, 24480, 24528, 24540, 24600,
  24660, 24696, 24720, 24780, 24840, 24864, 24900, 24960, 25020, 25032,
  25080, 25116, 25140, 25200, 25260, 25308, 25320, 25368, 25380, 25440,
  25500, 25536, 25560, 25620, 25680, 25704, 25740, 25800, 25860, 25872,
  25920, 25980, 26040, 26100, 26160, 26208, 26220, 26280, 26340, 26376,
  26400, 26460, 26520, 26544, 26580, 26640, 26700, 26712, 26760, 26820,
  26880, 26928, 26940, 27000, 27048, 27060, 27120, 27180, 27216, 27240,
  27300, 27360, 27384, 27420, 27480, 27540, 27552, 27600, 27660, 27720,
  27780, 27840, 27888, 27900, 27960, 28020, 28056, 28080, 28140, 28200,
  28224, 28260, 28320, 28380, 28392, 28440, 28500, 28560, 28620, 28680,
  28728, 28740, 28800, 28860, 28896, 28920, 28980, 29040, 29064, 29100,
  29120, 29160, 29220, 29232, 29280, 29340, 29376, 29400, 29460, 29484,
  29520, 29568, 29580, 29640, 29700, 29736, 29760, 29820, 29880, 29904,
  29940, 30000, 30060, 30072, 30120, 30180, 30240, 30300, 30360, 30408,
  30420, 30480, 30540, 30576, 30600, 30660, 30720, 30744, 30780, 30840,
  30900, 30912, 30960, 31020, 31080, 31140, 31200, 31248, 31260, 31320,
  31380, 31416, 31440, 31500, 31560, 31584, 31620, 31668, 31680, 31740,
  31752, 31800, 31824, 31860, 31920, 31980, 32040, 32088, 32100, 32160,
  32220, 32256, 32280, 32340, 32400, 32424, 32460, 32520, 32580, 32592,
  32640, 32700, 32736, 32760, 32820, 32880, 32928, 32940, 33000, 33060,
  33096, 33120, 33180, 33240, 33264, 33300, 33360, 33420, 33432, 33480,
  33540, 33600, 33660, 33696, 33720, 33768, 33780, 33840, 33852, 33900,
  33936, 33960, 34020, 34080, 34104, 34140, 34200, 34260, 34272, 34320,
  34380, 34440, 34500, 34560, 34608, 34620, 34680, 34740, 34776, 34800,
  34860, 34920, 34944, 34980, 35040, 35100, 35112, 35160, 35220, 35280,
  35340, 35400, 35448, 35460, 35520, 35580, 35616, 35640, 35700, 35760,
  35784, 35820, 35880, 35940, 35952, 36000, 36036, 36060, 36120, 36180,
  36240, 36288, 36300, 36360, 36420, 36432, 36456, 36480, 36540, 36600,
  36624, 36660, 36720, 36780, 36792, 36840, 36900, 36960, 37020, 37080,
  37128, 37140, 37200, 37260, 37296, 37320, 37380, 37440, 37464, 37500,
  37560, 37620, 37632, 37680, 37740, 37800, 37860, 37920, 37968, 37980,
  38040, 38100, 38136, 38160, 38220, 38280, 38304, 38340, 38400, 38460,
  38472, 38520, 38580, 38640, 38700, 38760, 38808, 38820, 38880, 38940,
  38976, 39000, 39060, 39120, 39144, 39168, 39180, 39240, 39300, 39312,
  39360, 39420, 39480, 39540, 39600, 39648, 39660, 39720, 39732, 39780,
  39816, 39840, 39900, 39960, 39984, 40020, 40080, 40140, 40152, 40200,
  40260, 40320, 40380, 40404, 40440, 40488, 40500, 40560, 40620, 40656,
  40680, 40740, 40800, 40824, 40860, 40920, 40980, 40992, 41040, 41100,
  41160, 41220, 41280, 41328, 41340, 41400, 41460, 41496, 41520, 41580,
  41616, 41640, 41664, 41700, 41760, 41820, 41832, 41880, 41940, 42000,
  42060, 42120, 42168, 42180, 42240, 42300, 42336, 42360, 42420, 42480,
  42504, 42540, 42588, 42600, 42660, 42672, 42720, 42780, 42840, 42900,
  42960, 43008, 43020, 43080, 43140, 43176, 43200, 43260, 43320, 43344,
  43380, 43440, 43500, 43512, 43560, 43620, 43680, 43740, 43800, 43848,
  43860, 43920, 43980, 44016, 44040, 44064, 44100, 44160, 44184, 44220,
  44280, 44340, 44352, 44400, 44460, 44520, 44580, 44640, 44688, 44700,
  44760, 44772, 44820, 44856, 44880, 44928, 44940, 45000, 45024, 45060,
  45120, 45180, 45192, 45240, 45300, 45360, 45420, 45480, 45528, 45540,
  45600, 45660, 45696, 45720, 45780, 45840, 45864, 45900, 45960, 46020,
  46032, 46080, 46140, 46200, 46260, 46320, 46368, 46380, 46440, 46500,
  46512, 46536, 46560, 46620, 46680, 46704, 46740, 46800, 46860, 46872,
  46920, 46956, 46980, 47040, 47100, 47160, 47208, 47220, 47280, 47340,
  47376, 47400, 47460, 47520, 47544, 47580, 47640, 47700, 47712, 47760,
  47820, 47880, 47940, 48000, 48048, 48060, 48120, 48180, 48216, 48240,
  48300, 48360, 48384, 48420, 48480, 48540, 48552, 48576, 48600, 48660,
  48720, 48780, 48840, 48888, 48900, 48960, 49020, 49056, 49080, 49140,
  49200, 49224, 49260, 49320, 49380, 49392, 49440, 49500, 49560, 49620,
  49680, 49728, 49740, 49800, 49860, 49896, 49920, 49980 ];

# reader for already computed groups. Claude Code

##  Access functions for a library of groups computed so far
##  The data live in the subdirectory "groups", one file per order:
##  "groups<n>.grp" holds all groups of order <n> that have the property.
##  Each such file is a self-contained expression of the form
##
##      return [ <grp1>, <grp2>, ... ];
##
##  so that  ReadAsFunction( file )()  returns the list of these groups.
##
##  Exported functions:
##      NrNonsolvableGroups( n )   -- number of such groups of order n
##      NonsolvableGroup( n, i )   -- the i-th such group of order n
##

#############################################################################
##
##  Configuration.
##

# Directory containing the data files.  By default this is the subdirectory
# "groups" of GAP's current working directory; set it to an absolute path
# (e.g. Directory("/path/to/groups")) if the data live elsewhere.
NonsolvableGroupsDirectory := Directory( "computedgroups" );

# Largest order for which data are permitted.
NonsolvableGroupsMaxOrder := 50000;

# Cache of lists already read from disk, indexed by order.
NonsolvableGroupsCache := [];

#############################################################################
##
#F  NonsolvableGroupsData( <n> ) . . . . . list of all property-groups of order n
##
##  Internal helper: returns (and caches) the list stored in groups<n>.grp,
##  after validating the order.
##
NonsolvableGroupsData := function( n )
  local file, data;

  if not IsPosInt( n ) then
    Error( "<n> must be a positive integer" );
  fi;
  if n > NonsolvableGroupsMaxOrder then
    Error( "the order <n>=", n,
           " must not exceed ", NonsolvableGroupsMaxOrder );
  fi;

  # Serve from cache if we have already read this order.
  if IsBound( NonsolvableGroupsCache[n] ) then
    return NonsolvableGroupsCache[n];
  fi;

  file := Filename( NonsolvableGroupsDirectory,
                    Concatenation( "groups", String( n ), ".grp" ) );
  if file = fail or not IsReadableFile( file ) then
    Error( "no group data available for order ", n,
           " (file `groups", String( n ), ".grp' not found in ",
           Filename( NonsolvableGroupsDirectory, "" ), ")" );
  fi;

  data := ReadAsFunction( file )();
  if not IsList( data ) then
    Error( "the data file for order ", n, " did not evaluate to a list" );
  fi;

  NonsolvableGroupsCache[n] := data;
  return data;
end;

#############################################################################
##
#F  NrNonsolvableGroups( <n> ) . . . number of property-groups of order <n>
##
NrNonsolvableGroups := function( n )
  return Length( NonsolvableGroupsData( n ) );
end;

#############################################################################
##
#F  NonsolvableGroup( <n>, <i> ) . . . . . . i-th property-group of order <n>
##
NonsolvableGroup := function( n, i )
  local data;

  data := NonsolvableGroupsData( n );

  if not IsPosInt( i ) then
    Error( "<i> must be a positive integer" );
  fi;
  if i > Length( data ) then
    Error( "there are only ", Length( data ),
           " groups of order ", n, ", but index ", i, " was requested" );
  fi;

  return data[i];
end;

# store:
# PrintTo(Concatenation("computedgroups/groups",String(Size(l[1])),".grp"),
# "return ",l,";\n");


Read("ffgrps.g");
Read("tabletrans.g");

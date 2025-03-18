/* --------------------------------------------------------------------------
 * This is the Hugs compiler, handling translation of typechecked code to
 * `kernel' language, elimination of pattern matching and translation to
 * super combinators (lambda lifting).
 *
 * The Hugs 98 system is Copyright (c) Mark P Jones, Alastair Reid, the
 * Yale Haskell Group, and the OGI School of Science & Engineering at OHSU,
 * 1994-2003, All rights reserved.  It is distributed as free software under
 * the license in the file "License", which is included in the distribution.
 *
 * $RCSfile: compiler.c,v $
 * $Revision: 1.25 $
 * $Date: 2003/12/04 13:53:50 $
 * ------------------------------------------------------------------------*/

#include "prelude.h"
#include "storage.h"
#include "connect.h"
#include "errors.h"
#include "goal.h"
#include "char.h"
#include "output.h"	/* needed for DEBUG_CODE|DEBUG_SHOWSC */
#include "opts.h"	/* needed for DEBUG_SHOWSC */

Addr inputCode;                        /* Addr of compiled code for expr   */
static Name currentName;               /* Top level name being processed   */
#if DEBUG_SHOWSC
static FILE *scfp;		       /* super combinator file pointer    */
#endif

/* --------------------------------------------------------------------------
 * Local function prototypes:
 * ------------------------------------------------------------------------*/

static Cell local translate             Args((Cell));
static Void local transPair             Args((Pair));
static Void local transTriple           Args((Triple));
static Void local transAlt              Args((Cell));
static Void local transCase             Args((Cell));
static List local transBinds            Args((List));
static Cell local transRhs              Args((Cell));
static Cell local mkConsList            Args((List));
static Cell local expandLetrec          Args((Cell));
static Cell local transComp             Args((Cell,List,Cell));
static Cell local transDo               Args((Cell,Cell,List));
static Cell local transConFlds          Args((Cell,List));
static Cell local transUpdFlds          Args((Cell,List,List));

#if MUDO
static Cell local transMDo		Args((Cell,Cell,List));
static Cell local mdoBuildTuple		Args((List));
#endif

static Cell local refutePat             Args((Cell));
static Cell local refutePatAp           Args((Cell));
static Cell local matchPat              Args((Cell));
static List local remPat                Args((Cell,Cell,List));
static List local remPat1               Args((Cell,Cell,List));

static Cell local pmcTerm               Args((Int,List,Cell));
static Cell local pmcPair               Args((Int,List,Pair));
static Cell local pmcTriple             Args((Int,List,Triple));
static Cell local pmcVar                Args((List,Text));
static Void local pmcLetrec             Args((Int,List,Pair));
static Cell local pmcVarDef             Args((Int,List,List));
static Void local pmcFunDef             Args((Int,List,Triple));
static List local altsMatch             Args((Int,Int,List,List));
static Cell local match                 Args((Int,List));
static Cell local joinMas               Args((Int,List));
static Bool local canFail               Args((Cell));
static List local addConTable           Args((Cell,Cell,List));
static Void local advance               Args((Int,Int,Cell));
static Bool local emptyMatch            Args((Cell));
static Cell local maDiscr               Args((Cell));
static Bool local isNumDiscr            Args((Cell));
static Bool local eqNumDiscr            Args((Cell,Cell));
#if TREX
static Bool local isExtDiscr            Args((Cell));
static Bool local eqExtDiscr            Args((Cell,Cell));
#endif

static Cell local lift                  Args((Int,List,Cell));
static Void local liftPair              Args((Int,List,Pair));
static Void local liftTriple            Args((Int,List,Triple));
static Void local liftAlt               Args((Int,List,Cell));
static Void local liftNumcase           Args((Int,List,Triple));
static Cell local liftVar               Args((List,Cell));
static Cell local liftLetrec            Args((Int,List,Cell));
static Void local liftFundef            Args((Int,List,Triple));
static Void local solve                 Args((List));

static Cell local preComp               Args((Cell));
static Cell local preCompPair           Args((Pair));
static Cell local preCompTriple         Args((Triple));
static Void local preCompCase           Args((Pair));
static Cell local preCompOffset         Args((Int));

static Void local compileGlobalFunction Args((Pair));
static Void local compileGenFunction	Args((Name));
static Name local compileSelFunction	Args((Pair));
static Void local newGlobalFunction     Args((Name,Int,List,Int,Cell));

#if DEBUG_SHOWSC
static Void local debugConstructors     Args((FILE *fp,Cell c));
static Void local debugConstructor      Args((FILE *fp,Name c));
#endif

/* --------------------------------------------------------------------------
 * Translation:    Convert input expressions into a less complex language
 *                 of terms using only LETREC, AP, constants and vars.
 *                 Also remove pattern definitions on lhs of eqns.
 * ------------------------------------------------------------------------*/

static Cell local translate(Cell e)         /* Translate expression:            */
{
    switch (whatIs(e)) {
	case LETREC     : snd(snd(e)) = translate(snd(snd(e)));
			  return expandLetrec(e);

	case COND       : transTriple(snd(e));
			  return e;

	case AP         : fst(e) = translate(fst(e));

			  if (fst(e)==nameId || fst(e)==nameInd)
			      return translate(snd(e));
			  if (isName(fst(e)) &&
			      isMfun(fst(e)) &&
			      mfunOf(fst(e))==0)
			      return translate(snd(e));

			  snd(e) = translate(snd(e));
			  return e;

#if BIGNUMS
	case POSNUM     :
	case ZERONUM    :
	case NEGNUM     : return e;
#endif
	case NAME       : if (e==nameOtherwise)
			      return nameTrue;
			  if (isCfun(e)) {
			      if (isName(name(e).defn))
				  return name(e).defn;
			      if (isPair(name(e).defn))
				  return snd(name(e).defn);
			  }
			  return e;

#if TREX
	case RECSEL     : return nameRecSel;

	case EXT        :
#endif
	case TUPLE      :
	case VAROPCELL  :
	case VARIDCELL  :
	case DICTVAR    :
	case INTCELL    :
	case DOUBLECELL :
	case STRCELL    :
	case CHARCELL   : return e;

#if IPARAM
	case IPVAR	: return nameId;
#endif

	case FINLIST    : mapOver(translate,snd(e));
			  return mkConsList(snd(e));

	case DOCOMP     : {   Cell m = translate(fst(snd(e)));
			      Cell r = translate(fst(snd(snd(e))));
			      return transDo(m,r,snd(snd(snd(e))));
			  }

	case MONADCOMP  : {   Cell m  = translate(fst(snd(e)));
			      Cell r  = translate(fst(snd(snd(e))));
			      Cell qs = snd(snd(snd(e)));
			      if (m == nameListMonad)
				  return transComp(r,qs,nameNil);
			      else {
#if MONAD_COMPS
				  r = ap(ap(nameReturn,m),r);
				  return transDo(m,r,qs);
#else
				  internal("translate: monad comps");
#endif
			      }
			  }
#if MUDO
	case MDOCOMP	: {   Cell m	= translate(fst(fst(snd(e))));
			      Cell ms	= translate(snd(fst(snd(e))));
			      Cell r	= translate(fst(snd(snd(e))));
			      Cell segs = snd(snd(snd(e)));
			      map2Over(transMDo,m,ms,segs);
			      return transDo(ms,r,segs);
			  }
#endif

	case CONFLDS    : return transConFlds(fst(snd(e)),snd(snd(e)));

	case UPDFLDS    : return transUpdFlds(fst3(snd(e)),
					      snd3(snd(e)),
					      thd3(snd(e)));

	case CASE       : {   Cell nv = inventVar();
			      mapProc(transCase,snd(snd(e)));
			      return ap(LETREC,
					pair(singleton(pair(nv,snd(snd(e)))),
					     ap(nv,translate(fst(snd(e))))));
			  }

	case LAMBDA     : {   Cell nv = inventVar();
			      transAlt(snd(e));
			      return ap(LETREC,
					pair(singleton(pair(
							nv,
							singleton(snd(e)))),
					     nv));
			  }

	default         : internal("translate");
    }
    return e;
}

static Void local transPair(Pair pr)        /* Translate each component in a    */
{                             /* pair of expressions.             */
    fst(pr) = translate(fst(pr));
    snd(pr) = translate(snd(pr));
}

static Void local transTriple(Triple tr)      /* Translate each component in a    */
{                           /* triple of expressions.           */
    fst3(tr) = translate(fst3(tr));
    snd3(tr) = translate(snd3(tr));
    thd3(tr) = translate(thd3(tr));
}

static Void local transAlt(Cell e)          /* Translate alt:                   */
{                              /* ([Pat], Rhs) ==> ([Pat], Rhs')   */
    snd(e) = transRhs(snd(e));
}

static Void local transCase(Cell c)         /* Translate case:                  */
{                              /* (Pat, Rhs) ==> ([Pat], Rhs')     */
    fst(c) = singleton(fst(c));
    snd(c) = transRhs(snd(c));
}

static List local transBinds(List bs)	/* Translate list of bindings:     */
{				/* eliminating pattern matching on */
    List newBinds = NIL;		/* lhs of bindings.                */
    for (; nonNull(bs); bs=tl(bs)) {
#if IPARAM
	Cell v = fst(hd(bs));
	while (isAp(v) && fun(v) == nameInd)
	    v = arg(v);
	fst(hd(bs)) = v;
	if (isVar(v)) {
#else
	  if (isVar(fst(hd(bs)))) {
#endif
	    mapProc(transAlt,snd(hd(bs)));
	    newBinds = cons(hd(bs),newBinds);
	}
	else
	    newBinds = remPat(fst(snd(hd(bs))),
			      snd(snd(hd(bs)))=transRhs(snd(snd(hd(bs)))),
			      newBinds);
    }
    return newBinds;
}

static Cell local transRhs(Cell rhs)        /* Translate rhs: removing line nos */
{
    switch (whatIs(rhs)) {
	case LETREC  : snd(snd(rhs)) = transRhs(snd(snd(rhs)));
		       return expandLetrec(rhs);

	case GUARDED : mapOver(snd,snd(rhs));       /* discard line number */
		       mapProc(transPair,snd(rhs));
		       return rhs;

	default      : return translate(snd(rhs));  /* discard line number */
    }
}

static Cell local mkConsList(List es)       /* Construct expression for list es */
{                             /* using nameNil and nameCons       */
    if (isNull(es))
	return nameNil;
    else
	return ap(ap(nameCons,hd(es)),mkConsList(tl(es)));
}

static Cell local expandLetrec(Cell root)   /* translate LETREC with list of    */
{                           /* groups of bindings (from depend. */
    Cell e   = snd(snd(root));         /* analysis) to use nested LETRECs  */
    List bss = fst(snd(root));
    Cell temp;

    if (isNull(bss))                   /* should never happen, but just in */
	return e;                      /* case:  LETREC [] IN e  ==>  e    */

    mapOver(transBinds,bss);           /* translate each group of bindings */

    for (temp=root; nonNull(tl(bss)); bss=tl(bss)) {
	fst(snd(temp)) = hd(bss);
	snd(snd(temp)) = ap(LETREC,pair(NIL,e));
	temp           = snd(snd(temp));
    }
    fst(snd(temp)) = hd(bss);

    return root;
}

/* --------------------------------------------------------------------------
 * Translation of list comprehensions is based on the description in
 * `The Implementation of Functional Programming Languages':
 *
 * [ e | qs ] ++ l            => transComp e qs l
 * transComp e []           l => e : l
 * transComp e ((p<-xs):qs) l => LETREC _h []      = l
 *                                      _h (p:_xs) = transComp e qs (_h _xs)
 *                                      _h (_:_xs) = _h _xs --if p !failFree
 *                               IN _h xs
 * transComp e (b:qs)       l => if b then transComp e qs l else l
 * transComp e (decls:qs)   l => LETREC decls IN transComp e qs l
 * ------------------------------------------------------------------------*/

static Cell local transComp(Cell e,List qs,Cell l)    /* Translate [e | qs] ++ l          */
{
    if (nonNull(qs)) {
	Cell q   = hd(qs);
	Cell qs1 = tl(qs);

	switch (fst(q)) {
	    case FROMQUAL : {   Cell ld    = NIL;
				Cell hVar  = inventVar();
				Cell xsVar = inventVar();

				if (!failFree(fst(snd(q))))
				    ld = cons(pair(singleton(
						    ap(ap(nameCons,
							  WILDCARD),
							  xsVar)),
						   ap(hVar,xsVar)),
					      ld);

				ld = cons(pair(singleton(
						ap(ap(nameCons,
						      fst(snd(q))),
						      xsVar)),
					       transComp(e,
							 qs1,
							 ap(hVar,xsVar))),
					  ld);
				ld = cons(pair(singleton(nameNil),
					       l),
					  ld);

				return ap(LETREC,
					  pair(singleton(pair(hVar,
							      ld)),
					       ap(hVar,
						  translate(snd(snd(q))))));
			    }

	    case QWHERE   : return
				expandLetrec(ap(LETREC,
						pair(snd(q),
						     transComp(e,qs1,l))));

	    case BOOLQUAL : return ap(COND,
				      triple(translate(snd(q)),
					     transComp(e,qs1,l),
					     l));
	}
    }

    return ap(ap(nameCons,e),l);
}

/* --------------------------------------------------------------------------
 * Translation of monad comprehensions written using do-notation:
 *
 * do { e }               =>  e
 * do { p <- exp; qs }    =>  LETREC _h p = do { qs }
 *                                   _h _ = fail m "match fails"
 *                            IN bind m exp _h
 * do { LET decls; qs }   =>  LETREC decls IN do { qs }
 * do { IF guard; qs }    =>  if guard then do { qs } else fail m  "guard fails"
 * do { exp; qs }         =>  (>>) m exp (do {qs})
 *
 * where m :: Monad f
 * ------------------------------------------------------------------------*/

static Cell local transDo(Cell m,Cell e,List qs)	/* Translate do { qs ; e }         */
{
    if (nonNull(qs)) {
	Cell q   = hd(qs);
	Cell qs1 = tl(qs);

	switch (fst(q)) {
	    case FROMQUAL : {   Cell ld   = NIL;
				Cell hVar = inventVar();

				if (!failFree(fst(snd(q)))) {
				    Cell str = mkStr(findText("match fails"));
				    ld = cons(pair(singleton(WILDCARD),
						   ap2(nameMFail,m,str)),
					      ld);
				}

				ld = cons(pair(singleton(fst(snd(q))),
					       transDo(m,e,qs1)),
					  ld);

				return ap(LETREC,
					  pair(singleton(pair(hVar,ld)),
					       ap(ap(ap(nameBind,
							m),
						     translate(snd(snd(q)))),
						  hVar)));
			    }

	    case DOQUAL :   return ap(ap(ap(nameThen,m),
					 translate(snd(q))),
				      transDo(m,e,qs1));

	    case QWHERE   : return
				expandLetrec(ap(LETREC,
						pair(snd(q),
						     transDo(m,e,qs1))));

	    case BOOLQUAL : return
				ap(COND,
				   triple(translate(snd(q)),
					  transDo(m,e,qs1),
					  ap2(nameMFail,m,
					    mkStr(findText("guard fails")))));
	}
    }
    return e;
}

#if MUDO
/* Copied verbatim from parser.y: */
static Cell local mdoBuildTuple(List tup)	/* build tuple (x1,...,xn) from	   */
{				/* list [xn,...,x1]		   */
    Int  n = 0;
    Cell t = tup;
    Cell x;

    do {				/*    .                    .	   */
	x      = fst(t);		/*   / \                  / \	   */
	fst(t) = snd(t);		/*  xn  .                .   xn	   */
	snd(t) = x;			/*       .    ===>      .	   */
	x      = t;			/*        .            .	   */
	t      = fun(x);		/*         .          .		   */
	n++;				/*        / \        / \	   */
    } while (nonNull(t));		/*       x1  NIL   (n)  x1	   */
    fst(x) = mkTuple(n);
    return tup;
}

static Cell local transMDo(Cell m,Cell ms,List seg)	/* translate each segment in an mdo */
{
    /* seg looks like: ((1,2,3),4)
	where:
	    1: rec vars of the segment
	    2: exp vars of the segment
	    3: def vars of the segment  (not used here)
	    4: list of qualifiers in the segment
    */

    List qs	  = snd(seg);
    List recs	  = fst3(fst(seg));
    List exps	  = snd3(fst(seg));
    Int  noOfRecs = length(recs);
    Int  noOfExps = length(exps);

    /* Case 1: Not a recursive segment. It must be the case that |qs| = 1 */
    if(isNull(recs)) {		
	if(length(qs)!=1) {		
	    internal("MDO: Non-recursive, non-singleton segment, Impossible!");
	}
	return hd(qs);
    } 

#define mkLambda(arg,body)	ap(LAMBDA,pair(singleton(arg),pair(0,body)))
#define mkDoComp(qs,exp)	ap(DOCOMP,pair(ms,pair(exp,qs)))
#define BIND(e1,e2)		ap3(nameBind,ms,e1,e2)
#define RET(e)			ap2(nameReturn,ms,e)
#define MFIX(arg,body)		ap2(nameMFix,m,mkLambda(arg,body))
#define fromQual(p,e)		pair(FROMQUAL,pair(p,e))
#define doQual(e)		pair(DOQUAL,e)

    /* Case 2: Segment is recursive, but there are no exported variables: */
    if(noOfExps == 0) {
	Cell RT  = noOfRecs==1 ? hd(recs) : mdoBuildTuple(recs);
	Cell pat = noOfRecs==1 ? RT : ap(LAZYPAT,RT);

	return doQual(MFIX(pat,mkDoComp(qs,RET(RT))));
    }

    /* Case 3: There is one exported variable, one rec variable, 
	       and they're the same */
    if(noOfRecs == 1 && noOfExps == 1 && varIsMember(textOf(hd(exps)),recs)) {
	Cell RT = hd(recs);

	return fromQual(RT,MFIX(RT,mkDoComp(qs,RET(RT))));
    }

    /* Case 4: There is one exported variable, >= 1 recursive vars, 
	       but exported variable is one of the recursives: */
    if(noOfExps == 1 && varIsMember(textOf(hd(exps)),recs)) {
	Cell RT	 = noOfRecs==1 ? hd(recs) : mdoBuildTuple(recs);
	Cell ET	 = hd(exps);
	Cell pat = noOfRecs==1 ? RT : ap(LAZYPAT,RT);

	return fromQual(ET,BIND(MFIX(pat,mkDoComp(qs,RET(RT))),
				mkLambda(RT,RET(ET))));
    }

    /* Case 5: There is only one exported variable, which is not recursive  */
    if(noOfExps == 1) {	
	Cell ET	 = hd(exps);
	Cell RT	 = mdoBuildTuple(cons(ET,recs));
	Cell pat = ap(LAZYPAT,RT);

	return fromQual(ET,BIND(MFIX(pat,mkDoComp(qs,RET(RT))),
				mkLambda(RT,RET(ET))));
    }

    /* Case 6: > 1 exports, no (apparent) optimization applicable: 
       Notice that this is also the "catch-all" phase */
    {	Cell nv	     = inventVar();
	Cell RT	     = mdoBuildTuple(cons(nv,recs));
	Cell ET	     = mdoBuildTuple(exps);
	Cell finQ    = fromQual(nv,RET(ET));
	Cell innerDo = mkDoComp(appendOnto(qs,singleton(finQ)),RET(RT));
	Cell pat     = ap(LAZYPAT,RT);

	return fromQual(ET,BIND(MFIX(pat,innerDo),mkLambda(RT,RET(nv))));
    }

#undef mkLambda
#undef mkDoComp
#undef BIND
#undef RET
#undef MFIX
#undef fromQual
#undef doQual
}

#endif

/* --------------------------------------------------------------------------
 * Translation of named field construction and update:
 *
 * Construction is implemented using the following transformation:
 *
 *   C{x1=e1, ..., xn=en} =  C v1 ... vm
 * where:
 *   vi = e1,        if the ith component of C is labelled with x1
 *       ...
 *      = en,        if the ith component of C is labelled with xn
 *      = undefined, otherwise
 *
 * Update is implemented using the following transformation:
 *
 *   e{x1=e1, ..., xn=en}
 *      =  let nv (C a1 ... am) v1 ... vn = C a1' .. am'
 *             nv (D b1 ... bk) v1 ... vn = D b1' .. bk
 *             ...
 *             nv _             v1 ... vn = error "failed update"
 *         in nv e e1 ... en
 * where:
 *   nv, v1, ..., vn, a1, ..., am, b1, ..., bk, ... are new variables,
 *   C,D,... = { K | K is a constr fun s.t. {x1,...,xn} subset of sels(K)}
 * and:
 *   ai' = v1,   if the ith component of C is labelled with x1
 *       ...
 *       = vn,   if the ith component of C is labelled with xn
 *       = ai,   otherwise
 *  etc...
 *
 * The error case may be omitted if C,D,... is an enumeration of all of the
 * constructors for the datatype concerned.  Strictly speaking, error case
 * isn't needed at all -- the only benefit of including it is that the user
 * will get a "failed update" message rather than a cryptic {v354 ...}.
 * So, for now, we'll go with the second option!
 *
 * For the time being, code for each update operation is generated
 * independently of any other updates.  However, if updates are used
 * frequently, then we might want to consider changing the implementation
 * at a later stage to cache definitions of functions like nv above.  This
 * would create a shared library of update functions, indexed by a set of
 * constructors {C,D,...}.
 * ------------------------------------------------------------------------*/

static Cell local transConFlds(Name c,List flds)  /* Translate C{flds}               */
{
    Cell e = c;
    Int  m = name(c).arity;
    Int  i;
    Text t = name(c).text;
    Cell tStr   = mkStr(t);
    Cell empty  = ap(namePrimThrow, ap(nameRecConError, tStr));

    for (i=m; i>0; i--) {
	e = ap(e,empty);
    }
    for (; nonNull(flds); flds=tl(flds)) {
	Cell a = e;
	for (i=m-sfunPos(fst(hd(flds)),c); i>0; i--)
	    a = fun(a);
	arg(a) = translate(snd(hd(flds)));
    }
    return e;
}

static Cell local transUpdFlds(Cell e,List cs,List flds)/* Translate e{flds}              */
{
    Cell nv   = inventVar();
    Cell body = ap(nv,translate(e));
    List fs   = flds;
    List args = NIL;
    List alts = NIL;

    for (; nonNull(fs); fs=tl(fs)) {    /* body = nv e1 ... en             */
	Cell b = hd(fs);                /* args = [v1, ..., vn]            */
	body   = ap(body,translate(snd(b)));
	args   = cons(inventVar(),args);
    }

    for (; nonNull(cs); cs=tl(cs)) {    /* Loop through constructors to    */
	Cell c   = hd(cs);              /* build up list of alts.          */
	Cell pat = c;
	Cell rhs = c;
	List as  = args;
	Int  m   = name(c).arity;
	Int  i;

	for (i=m; i>0; i--) {           /* pat  = C a1 ... am              */
	    Cell a = inventVar();       /* rhs  = C a1 ... am              */
	    pat    = ap(pat,a);
	    rhs    = ap(rhs,a);
	}

	for (fs=flds; nonNull(fs); fs=tl(fs), as=tl(as)) {
	    Name s = fst(hd(fs));       /* Replace approp ai in rhs with   */
	    Cell r = rhs;               /* vars from [v1,...,vn]           */
	    for (i=m-sfunPos(s,c); i>0; i--)
		r = fun(r);
	    arg(r) = hd(as);
	}

	alts     = cons(pair(cons(pat,args),rhs),alts);
    }
    return ap(LETREC,pair(singleton(pair(nv,alts)),body));
}

/* --------------------------------------------------------------------------
 * Elimination of pattern bindings:
 *
 * The following code adopts the definition of failure free patterns as given
 * in the Haskell 1.3 report; the term "irrefutable" is also used there for
 * a subset of the failure free patterns described here, but has no useful
 * role in this implementation.  Basically speaking, the failure free patterns
 * are:         variable, wildcard, ~apat
 *              var@apat,               if apat is failure free
 *              C apat1 ... apatn       if C is a product constructor
 *                                      (i.e. an only constructor) and
 *                                      apat1,...,apatn are failure free
 * Note that the last case automatically covers the case where C comes from
 * a newtype construction.
 * ------------------------------------------------------------------------*/

Bool failFree(Cell pat)                /* is pattern failure free?              */
{                       /* (can we omit the default case?)       */
    Cell c = getHead(pat);

    switch (whatIs(c)) {
	case ASPAT     : return failFree(snd(snd(pat)));

	case NAME      : if (!isCfun(c) || cfunOf(c)!=0)
			     return FALSE;
			 /*intentional fall-thru*/
	case TUPLE     : for (; isAp(pat); pat=fun(pat))
			     if (!failFree(arg(pat)))
				return FALSE;
			 /*intentional fall-thru*/
	case LAZYPAT   :
	case VAROPCELL :
	case VARIDCELL :
	case DICTVAR   :
	case WILDCARD  : return TRUE;

#if TREX
	case EXT       : return failFree(extField(pat)) &&
				failFree(extRow(pat));
#endif

	case CONFLDS   : if (cfunOf(fst(snd(c)))==0) {
			     List fs = snd(snd(c));
			     for (; nonNull(fs); fs=tl(fs))
				 if (!failFree(snd(hd(fs))))
				     return FALSE;
			     return TRUE;
			 }
			 /*intentional fall-thru*/
	default        : return FALSE;
    }
}

static Cell local refutePat(Cell pat)  /* find pattern to refute in conformality*/
{                       /* test with pat.                        */
				  /* e.g. refPat  (x:y) == (_:_)           */
				  /*      refPat ~(x:y) == _      etc..    */

    switch (whatIs(pat)) {
	case ASPAT     : return refutePat(snd(snd(pat)));

	case FINLIST   : {   Cell ys = snd(pat);
			     Cell xs = NIL;
			     for (; nonNull(ys); ys=tl(ys))
				 xs = ap(ap(nameCons,refutePat(hd(ys))),xs);
			     return revOnto(xs,nameNil);
			 }

	case CONFLDS   : {   Cell ps = NIL;
			     Cell fs = snd(snd(pat));
			     for (; nonNull(fs); fs=tl(fs)) {
				 Cell p = refutePat(snd(hd(fs)));
				 ps     = cons(pair(fst(hd(fs)),p),ps);
			     }
			     return pair(CONFLDS,pair(fst(snd(pat)),rev(ps)));
			 }

	case VAROPCELL :
	case VARIDCELL :
	case DICTVAR   :
	case WILDCARD  :
	case LAZYPAT   : return WILDCARD;

	case STRCELL   :
	case CHARCELL  :
#if NPLUSK
	case ADDPAT    :
#endif
	case TUPLE     :
	case NAME      : return pat;

	case AP        : return refutePatAp(pat);

	default        : internal("refutePat");
			 return NIL; /*NOTREACHED*/
    }
}

static Cell local refutePatAp(Cell p)  /* find pattern to refute in conformality*/
{
    Cell h = getHead(p);
    if (h==nameFromInt || h==nameFromInteger || h==nameFromDouble)
	return p;
#if NPLUSK
    else if (whatIs(h)==ADDPAT)
	return ap(fun(p),refutePat(arg(p)));
#endif
#if TREX
    else if (isExt(h)) {
	Cell pf = refutePat(extField(p));
	Cell pr = refutePat(extRow(p));
	return ap(ap(fun(fun(p)),pf),pr);
    }
#endif
    else {
	List as = getArgs(p);
	mapOver(refutePat,as);
	return applyToArgs(h,as);
    }
}

static Cell local matchPat(Cell pat) /* find pattern to match against           */
{                     /* replaces parts of pattern that do not   */
				/* include variables with wildcards        */
    switch (whatIs(pat)) {
	case ASPAT     : {   Cell p = matchPat(snd(snd(pat)));
			     return (p==WILDCARD) ? fst(snd(pat))
						  : ap(ASPAT,
						       pair(fst(snd(pat)),p));
			 }

	case FINLIST   : {   Cell ys = snd(pat);
			     Cell xs = NIL;
			     for (; nonNull(ys); ys=tl(ys))
				 xs = cons(matchPat(hd(ys)),xs);
			     while (nonNull(xs) && hd(xs)==WILDCARD)
				 xs = tl(xs);
			     for (ys=nameNil; nonNull(xs); xs=tl(xs))
				 ys = ap(ap(nameCons,hd(xs)),ys);
			     return ys;
			 }

	case CONFLDS   : {   Cell ps   = NIL;
			     Name c    = fst(snd(pat));
			     Cell fs   = snd(snd(pat));
			     Bool avar = FALSE;
			     for (; nonNull(fs); fs=tl(fs)) {
				 Cell p = matchPat(snd(hd(fs)));
				 ps     = cons(pair(fst(hd(fs)),p),ps);
				 if (p!=WILDCARD)
				     avar = TRUE;
			     }
			     return avar ? pair(CONFLDS,pair(c,rev(ps)))
					 : WILDCARD;
			 }

	case VAROPCELL :
	case VARIDCELL :
	case DICTVAR   : return pat;

	case LAZYPAT   : {   Cell p = matchPat(snd(pat));
			     return (p==WILDCARD) ? WILDCARD : pat;
			 }

	case WILDCARD  :
	case STRCELL   :
	case CHARCELL  : return WILDCARD;

	case TUPLE     :
	case NAME      :
	case AP        : {   Cell h = getHead(pat);
			     if (h==nameFromInt     ||
				 h==nameFromInteger || h==nameFromDouble)
				 return WILDCARD;
#if NPLUSK
			     else if (whatIs(h)==ADDPAT)
				 return pat;
#endif
#if TREX
			     else if (isExt(h)) {
				 Cell pf = matchPat(extField(pat));
				 Cell pr = matchPat(extRow(pat));
				 return (pf==WILDCARD && pr==WILDCARD)
					  ? WILDCARD
					  : ap(ap(fun(fun(pat)),pf),pr);
			     }
#endif
			     else {
				 List args = NIL;
				 Bool avar = FALSE;
				 for (; isAp(pat); pat=fun(pat)) {
				     Cell p = matchPat(arg(pat));
				     if (p!=WILDCARD)
					 avar = TRUE;
				     args = cons(p,args);
				 }
				 return avar ? applyToArgs(pat,args)
					     : WILDCARD;
			     }
			 }

	default        : internal("matchPat");
			 return NIL; /*NOTREACHED*/
    }
}

#define addEqn(v,val,lds)  cons(pair(v,singleton(pair(NIL,val))),lds)

static List local remPat(Cell pat,Cell expr,List lds)
                         /* Produce list of definitions for eqn   */
                        /* pat = expr, including a conformality  */
{                       /* check if required.                    */
    Cell refPat = refutePat(pat);
    Cell varPat = matchPat(pat);

    if (varPat==WILDCARD)		     /* no vars => no equations    */
	return lds;

    /* Conformality test (if required):
     *   pat = expr  ==>    nv = LETREC confCheck nv@pat = nv
     *                           IN confCheck expr
     *                      remPat1(pat,nv,.....);
     */

    if (refPat!=WILDCARD) {
	Cell confVar = inventVar();
	Cell nv      = inventVar();
	Cell locfun  = pair(confVar,         /* confVar [([nv@refPat],nv)] */
			    singleton(pair(singleton(ap(ASPAT,
							pair(nv,refPat))),
					   nv)));

	if (whatIs(expr)==GUARDED) {         /* A spanner ... special case */
	    lds  = addEqn(nv,expr,lds);      /* for guarded pattern binding*/
	    expr = nv;
	    nv   = inventVar();
	}

	if (whatIs(varPat)==ASPAT) {         /* avoid using new variable if*/
	    nv     = fst(snd(varPat));       /* a variable is already given*/
	    varPat = snd(snd(varPat));       /* by an as-pattern           */
	}

	lds = addEqn(nv,                                /* nv =            */
		     ap(LETREC,pair(singleton(locfun),  /* LETREC [locfun] */
				    ap(confVar,expr))), /* IN confVar expr */
		     lds);

	return remPat1(varPat,nv,lds);
    }

    return remPat1(varPat,expr,lds);
}

static List local remPat1(Cell pat,Cell expr,List lds)
                         /* Add definitions for: pat = expr to    */
                        /* list of local definitions in lds.     */
{
    Cell c = getHead(pat);

    switch (whatIs(c)) {
	case WILDCARD  :
	case STRCELL   :
	case CHARCELL  : break;

	case ASPAT     : return remPat1(snd(snd(pat)),     /* v@pat = expr */
					fst(snd(pat)),
					addEqn(fst(snd(pat)),expr,lds));

	case LAZYPAT   : {   Cell nv;

			     if (isVar(expr) || isName(expr))
				 nv  = expr;
			     else {
				 nv  = inventVar();
				 lds = addEqn(nv,expr,lds);
			     }

			     return remPat(snd(pat),nv,lds);
			 }

#if NPLUSK
	case ADDPAT    : 
	  { Cell dict = arg(fun(pat));
	    /* I don't really know what I'm doing here, but
	     * when evaluating an expression like
	     *
	     *    Prelude> let (x+4) = 5 in x
	     *
	     * this results in primSub being passed a dict indirection.
	     * As far as I can gather, a dict indirection is a compile-time
	     * construction only, so shorten it out here. 
	     * 
	     * sof 2/03.
	     */
	    while(isAp(dict) && fun(dict) == nameInd) {
	      dict = arg(dict);
	    }
	    return remPat1(arg(pat),       /* n + k = expr */
			   ap(ap(ap(namePmSub,
				    dict),
				 mkInt(snd(fun(fun(pat))))),
			      expr),
			   lds);
	  }
#endif

	case FINLIST   : return remPat1(mkConsList(snd(pat)),expr,lds);

	case CONFLDS   : {   Name h  = fst(snd(pat));
			     Int  m  = name(h).arity;
			     Cell p  = h;
			     List fs = snd(snd(pat));
			     Int  i  = m;
			     while (0<i--)
				 p = ap(p,WILDCARD);
			     for (; nonNull(fs); fs=tl(fs)) {
				 Cell r = p;
				 for (i=m-sfunPos(fst(hd(fs)),h); i>0; i--)
				     r = fun(r);
				 arg(r) = snd(hd(fs));
			     }
			     return remPat1(p,expr,lds);
			 }

	case DICTVAR   : /* shouldn't really occur */
	case VARIDCELL :
	case VAROPCELL : return addEqn(pat,expr,lds);

	case NAME      : if (c==nameFromInt || c==nameFromInteger
					    || c==nameFromDouble) {
			     if (argCount==2)
				 arg(fun(pat)) = translate(arg(fun(pat)));
			     break;
			 }

			 if (argCount==1 && isCfun(c)	    /* for newtype */
			     && cfunOf(c)==0 && name(c).defn==nameId)
			     return remPat1(arg(pat),expr,lds);

			 /* intentional fall-thru */
	case TUPLE     : {   List ps = getArgs(pat);

			     if (nonNull(ps)) {
				 Cell nv, sel;
				 Int  i;

				 if (isVar(expr) || isName(expr))
				     nv  = expr;
				 else {
				     nv  = inventVar();
				     lds = addEqn(nv,expr,lds);
				 }

				 sel = ap(ap(nameSel,c),nv);
				 for (i=1; nonNull(ps); ++i, ps=tl(ps))
				      lds = remPat1(hd(ps),
						    ap(sel,mkInt(i)),
						    lds);
			     }
			 }
			 break;

#if TREX
	case EXT       : {   Cell nv = inventVar();
			     arg(fun(fun(pat)))
				 = translate(arg(fun(fun(pat))));
			     lds = addEqn(nv,
					  ap(ap(nameRecBrk,
						arg(fun(fun(pat)))),
					     expr),
					  lds);
			     lds = remPat1(extField(pat),ap(nameFst,nv),lds);
			     lds = remPat1(extRow(pat),ap(nameSnd,nv),lds);
			 }
			 break;
#endif

	default        : internal("remPat1");
			 break;
    }
    return lds;
}

/* --------------------------------------------------------------------------
 * Eliminate pattern matching in function definitions -- pattern matching
 * compiler:
 *
 * The original Gofer/Hugs pattern matching compiler was based on Wadler's
 * algorithms described in `Implementation of functional programming
 * languages'.  That should still provide a good starting point for anyone
 * wanting to understand this part of the system.  However, the original
 * algorithm has been generalized and restructured in order to implement
 * new features added in Haskell 1.3.
 *
 * During the translation, in preparation for later stages of compilation,
 * all local and bound variables are replaced by suitable offsets, and
 * locally defined function symbols are given new names (which will
 * eventually be their names when lifted to make top level definitions).
 * ------------------------------------------------------------------------*/

static Offset freeBegin; /* only variables with offset <= freeBegin are of */
static List   freeVars;  /* interest as `free' variables                   */
static List   freeFuns;  /* List of `free' local functions                 */

static Cell local pmcTerm(Int co,List sc,Cell e)     /* apply pattern matching compiler  */
                               /* co = current offset              */
                               /* sc = scope                       */
{                             /* e  = expr to transform           */
    switch (whatIs(e)) {
	case GUARDED  : map2Over(pmcPair,co,sc,snd(e));
			break;

	case LETREC   : pmcLetrec(co,sc,snd(e));
			break;

	case VARIDCELL:
	case VAROPCELL:
	case DICTVAR  : return pmcVar(sc,textOf(e));

	case COND     : return ap(COND,pmcTriple(co,sc,snd(e)));

	case AP       : return pmcPair(co,sc,e);

#if BIGNUMS
	case POSNUM   :
	case ZERONUM  :
	case NEGNUM   :
#endif
#if NPLUSK
	case ADDPAT   :
#endif
#if TREX
	case EXT      :
#endif
	case TUPLE    :
	case NAME     :
	case CHARCELL :
	case INTCELL  :
	case DOUBLECELL:
	case STRCELL  : break;

	default       : internal("pmcTerm");
			break;
    }
    return e;
}

static Cell local pmcPair(Int co,List sc,Pair pr)    /* apply pattern matching compiler  */
                               /* to a pair of exprs               */
{
    return pair(pmcTerm(co,sc,fst(pr)),
		pmcTerm(co,sc,snd(pr)));
}

static Cell local pmcTriple(Int co,List sc,Triple tr)  /* apply pattern matching compiler  */
                            /* to a triple of exprs             */
{
    return triple(pmcTerm(co,sc,fst3(tr)),
		  pmcTerm(co,sc,snd3(tr)),
		  pmcTerm(co,sc,thd3(tr)));
}

static Cell local pmcVar(List sc,Text t)         /* find translation of variable     */
                               /* in current scope                 */
{
    List xs;
    Name n;

    for (xs=sc; nonNull(xs); xs=tl(xs)) {
	Cell x = hd(xs);
	if (t==textOf(fst(x))) {
	    if (isOffset(snd(x))) {                  /* local variable ... */
		if (snd(x)<=freeBegin && !cellIsMember(snd(x),freeVars))
		    freeVars = cons(snd(x),freeVars);
		return snd(x);
	    }
	    else {                                   /* local function ... */
		if (!cellIsMember(snd(x),freeFuns))
		    freeFuns = cons(snd(x),freeFuns);
		return fst3(snd(x));
	    }
	}
    }

    if (isNull(n=findName(t)))         /* Lookup global name - the only way*/
	n = newName(t,currentName);    /* this (should be able to happen)  */
				       /* is with new global var introduced*/
				       /* after type check; e.g. remPat1   */
    return n;
}

static Void local pmcLetrec(Int co,List sc,Pair e)   /* apply pattern matching compiler  */
                               /* to LETREC, splitting decls into  */
                               /* two sections                     */
{
    List fs = NIL;                     /* local function definitions       */
    List vs = NIL;                     /* local variable definitions       */
    List ds;

    for (ds=fst(e); nonNull(ds); ds=tl(ds)) {      /* Split decls into two */
	Cell v     = fst(hd(ds));
	Int  arity = length(fst(hd(snd(hd(ds)))));

	if (arity==0) {                            /* Variable declaration */
	    vs = cons(snd(hd(ds)),vs);
	    sc = cons(pair(v,mkOffset(++co)),sc);
	}
	else {                                     /* Function declaration */
	    fs = cons(triple(inventVar(),mkInt(arity),snd(hd(ds))),fs);
	    sc = cons(pair(v,hd(fs)),sc);
	}
    }
    vs       = rev(vs);                /* Put declaration lists back in    */
    fs       = rev(fs);                /* original order                   */
    fst(e)   = pair(vs,fs);            /* Store declaration lists          */
    map2Over(pmcVarDef,co,sc,vs);      /* Translate variable definitions   */
    map2Proc(pmcFunDef,co,sc,fs);      /* Translate function definitions   */
    snd(e)   = pmcTerm(co,sc,snd(e));  /* Translate LETREC body            */
    freeFuns = diffList(freeFuns,fs);  /* Delete any `freeFuns' bound in fs*/
}

static Cell local pmcVarDef(Int co,List sc,List vd)  /* apply pattern matching compiler  */
                               /* to variable definition           */
{                             /* vd :: [ ([], rhs) ]              */
    Cell d = snd(hd(vd));
    if (nonNull(tl(vd)) && canFail(d))
	return ap(FATBAR,pair(pmcTerm(co,sc,d),
			      pmcVarDef(co,sc,tl(vd))));
    return pmcTerm(co,sc,d);
}

static Void local pmcFunDef(Int co,List sc,Triple fd)  /* apply pattern matching compiler  */
                             /* to function definition           */
{                           /* fd :: (Var, Arity, [Alt])        */
    Offset saveFreeBegin = freeBegin;
    List   saveFreeVars  = freeVars;
    List   saveFreeFuns  = freeFuns;
    Int    arity         = intOf(snd3(fd));
    Cell   temp          = altsMatch(co+1,arity,sc,thd3(fd));
    Cell   xs;

    freeBegin = mkOffset(co);
    freeVars  = NIL;
    freeFuns  = NIL;
    temp      = match(co+arity,temp);
    thd3(fd)  = triple(freeVars,freeFuns,temp);

    for (xs=freeVars; nonNull(xs); xs=tl(xs))
	if (hd(xs)<=saveFreeBegin && !cellIsMember(hd(xs),saveFreeVars))
	    saveFreeVars = cons(hd(xs),saveFreeVars);

    for (xs=freeFuns; nonNull(xs); xs=tl(xs))
	if (!cellIsMember(hd(xs),saveFreeFuns))
	    saveFreeFuns = cons(hd(xs),saveFreeFuns);

    freeBegin = saveFreeBegin;
    freeVars  = saveFreeVars;
    freeFuns  = saveFreeFuns;
}

/* ---------------------------------------------------------------------------
 * Main part of pattern matching compiler: convert [Alt] to case constructs
 *
 * This section of Hugs has been almost completely rewritten to be more
 * general, in particular, to allow pattern matching in orders other than the
 * strictly left-to-right approach of the previous version.  This is needed
 * for the implementation of the so-called Haskell 1.3 `record' syntax.
 *
 * At each stage, the different branches for the cases to be considered
 * are represented by a list of values of type:
 *   Match ::= { maPats :: [Pat],       patterns to match
 *               maOffs :: [Offs],      offsets of corresponding values
 *               maSc   :: Scope,       mapping from vars to offsets
 *               maRhs  :: Rhs }        right hand side
 * [Implementation uses nested pairs, ((pats,offs),(sc,rhs)).]
 *
 * The Scope component has type:
 *   Scope  ::= [(Var,Expr)]
 * and provides a mapping from variable names to offsets used in the matching
 * process.
 *
 * Matches can be normalized by reducing them to a form in which the list
 * of patterns is empty (in which case the match itself is described as an
 * empty match), or in which the list is non-empty and the first pattern is
 * one that requires either a CASE or NUMCASE (or EXTCASE) to decompose.
 * ------------------------------------------------------------------------*/

#define mkMatch(ps,os,sc,r)     pair(pair(ps,os),pair(sc,r))
#define maPats(ma)              fst(fst(ma))
#define maOffs(ma)              snd(fst(ma))
#define maSc(ma)                fst(snd(ma))
#define maRhs(ma)               snd(snd(ma))
#define extSc(v,o,ma)           maSc(ma) = cons(pair(v,o),maSc(ma))

static List local altsMatch(Int co,Int n,List sc,List as) /* Make a list of matches from list*/
                                /* of Alts, with initial offsets   */
                                 /* reverse (take n [co..])         */
{
    List mas = NIL;
    List us  = NIL;
    for (; n>0; n--)
	us = cons(mkOffset(co++),us);
    for (; nonNull(as); as=tl(as))      /* Each Alt is ([Pat], Rhs)        */
	mas = cons(mkMatch(fst(hd(as)),us,sc,snd(hd(as))),mas);
    return rev(mas);
}

static Cell local match(Int co,List mas) /* Generate case statement for Matches mas */
                       /* at current offset co                    */
{                     /* N.B. Assumes nonNull(mas).              */
    Cell srhs = NIL;            /* Rhs for selected matches                */
    List smas = mas;            /* List of selected matches                */
    mas       = tl(mas);
    tl(smas)  = NIL;

    if (emptyMatch(hd(smas))) {         /* The case for empty matches:     */
	while (nonNull(mas) && emptyMatch(hd(mas))) {
	    List temp = tl(mas);
	    tl(mas)   = smas;
	    smas      = mas;
	    mas       = temp;
	}
	srhs = joinMas(co,rev(smas));
    }
    else {                              /* Non-empty match                 */
	Int  o = offsetOf(hd(maOffs(hd(smas))));
	Cell d = maDiscr(hd(smas));
	if (isNumDiscr(d)) {            /* Numeric match                   */
	    Int  da = discrArity(d);
	    Cell d1 = pmcTerm(co,maSc(hd(smas)),d);
	    while (nonNull(mas) && !emptyMatch(hd(mas))
				&& o==offsetOf(hd(maOffs(hd(mas))))
				&& isNumDiscr(d=maDiscr(hd(mas)))
				&& eqNumDiscr(d,d1)) {
		List temp = tl(mas);
		tl(mas)   = smas;
		smas      = mas;
		mas       = temp;
	    }
	    smas = rev(smas);
	    map2Proc(advance,co,da,smas);
	    srhs = ap(NUMCASE,triple(mkOffset(o),d1,match(co+da,smas)));
	}
#if TREX
	else if (isExtDiscr(d)) {       /* Record match                    */
	    Int  da = discrArity(d);
	    Cell d1 = pmcTerm(co,maSc(hd(smas)),d);
	    while (nonNull(mas) && !emptyMatch(hd(mas))
				&& o==offsetOf(hd(maOffs(hd(mas))))
				&& isExtDiscr(d=maDiscr(hd(mas)))
				&& eqExtDiscr(d,d1)) {
		List temp = tl(mas);
		tl(mas)   = smas;
		smas      = mas;
		mas       = temp;
	    }
	    smas = rev(smas);
	    map2Proc(advance,co,da,smas);
	    srhs = ap(EXTCASE,triple(mkOffset(o),d1,match(co+da,smas)));
	}
#endif
	else {                          /* Constructor match               */
	    List tab = addConTable(d,hd(smas),NIL);
	    Int  da;
	    while (nonNull(mas) && !emptyMatch(hd(mas))
				&& o==offsetOf(hd(maOffs(hd(mas))))
				&& !isNumDiscr(d=maDiscr(hd(mas)))) {
		tab = addConTable(d,hd(mas),tab);
		mas = tl(mas);
	    }
	    for (tab=rev(tab); nonNull(tab); tab=tl(tab)) {
		d    = fst(hd(tab));
		smas = snd(hd(tab));
		da   = discrArity(d);
		map2Proc(advance,co,da,smas);
		srhs = cons(pair(d,match(co+da,smas)),srhs);
	    }
	    srhs = ap(CASE,pair(mkOffset(o),srhs));
	}
    }
    return nonNull(mas) ? ap(FATBAR,pair(srhs,match(co,mas))) : srhs;
}

static Cell local joinMas(Int co,List mas)       /* Combine list of matches into rhs*/
                                /* using FATBARs as necessary      */
{                             /* Non-empty list of empty matches */
    Cell ma  = hd(mas);
    Cell rhs = pmcTerm(co,maSc(ma),maRhs(ma));
    if (nonNull(tl(mas)) && canFail(rhs))
	return ap(FATBAR,pair(rhs,joinMas(co,tl(mas))));
    else
	return rhs;
}

static Bool local canFail(Cell rhs)         /* Determine if expression (as rhs) */
{                            /* might ever be able to fail       */
    switch (whatIs(rhs)) {
	case LETREC  : return canFail(snd(snd(rhs)));
	case GUARDED : return TRUE;    /* could get more sophisticated ..? */
	default      : return FALSE;
    }
}

/* type Table a b = [(a, [b])]
 *
 * addTable                 :: a -> b -> Table a b -> Table a b
 * addTable x y []           = [(x,[y])]
 * addTable x y (z@(n,sws):zs)
 *              | n == x     = (n,sws++[y]):zs
 *              | otherwise  = (n,sws):addTable x y zs
 */

static List local addConTable(Cell x,Cell y,List tab) /* add element (x,y) to table       */
{
    if (isNull(tab))
	return singleton(pair(x,singleton(y)));
    else if (fst(hd(tab))==x)
	snd(hd(tab)) = appendOnto(snd(hd(tab)),singleton(y));
    else
	tl(tab) = addConTable(x,y,tl(tab));

    return tab;
}

static Void local advance(Int co,Int a,Cell ma)      /* Advance non-empty match by      */
                                /* processing head pattern         */
                                 /* discriminator arity             */
{
    Cell p  = hd(maPats(ma));
    List ps = tl(maPats(ma));
    List us = tl(maOffs(ma));
    if (whatIs(p)==CONFLDS) {           /* Special case for record syntax  */
	Name c  = fst(snd(p));
	List fs = snd(snd(p));
	List qs = NIL;
	List vs = NIL;
	for (; nonNull(fs); fs=tl(fs)) {
	    vs = cons(mkOffset(co+a+1-sfunPos(fst(hd(fs)),c)),vs);
	    qs = cons(snd(hd(fs)),qs);
	}
	ps = revOnto(qs,ps);
	us = revOnto(vs,us);
    }
    else                                /* Normally just spool off patterns*/
	for (; a>0; --a) {              /* and corresponding offsets ...   */
	    us = cons(mkOffset(++co),us);
	    ps = cons(arg(p),ps);
	    p  = fun(p);
	}

    maPats(ma) = ps;
    maOffs(ma) = us;
}

/* --------------------------------------------------------------------------
 * Normalize and test for empty match:
 * ------------------------------------------------------------------------*/

static Bool local emptyMatch(Cell ma)/* Normalize and test to see if a given    */
{                      /* match, ma, is empty.                    */

    while (nonNull(maPats(ma))) {
	Cell p;
tidyHd: switch (whatIs(p=hd(maPats(ma)))) {
	    case LAZYPAT   : {   Cell nv   = inventVar();
				 maRhs(ma) = ap(LETREC,
						pair(remPat(snd(p),nv,NIL),
						     maRhs(ma)));
				 p         = nv;
			     }
			     /* intentional fall-thru */
	    case VARIDCELL :
	    case VAROPCELL :
	    case DICTVAR   : extSc(p,hd(maOffs(ma)),ma);
	    case WILDCARD  : maPats(ma) = tl(maPats(ma));
			     maOffs(ma) = tl(maOffs(ma));
			     continue;

	    /* So-called "as-patterns"are really just pattern intersections:
	     *    (p1@p2:ps, o:os, sc, e) ==> (p1:p2:ps, o:o:os, sc, e)
	     * (But the input grammar probably doesn't let us take
	     * advantage of this, so we stick with the special case
	     * when p1 is a variable.)
	     */
	    case ASPAT     : extSc(fst(snd(p)),hd(maOffs(ma)),ma);
			     hd(maPats(ma)) = snd(snd(p));
			     goto tidyHd;

	    case FINLIST   : hd(maPats(ma)) = mkConsList(snd(p));
			     return FALSE;

	    case STRCELL   : {   String s = textToStr(textOf(p));
				 for (p=NIL; *s!='\0'; )
				     p = ap(consChar(getStrChr(&s)),p);
				 hd(maPats(ma)) = revOnto(p,nameNil);
			     }
			     return FALSE;

	    case AP        : if (isName(fun(p)) && isCfun(fun(p))
				 && cfunOf(fun(p))==0
				 && name(fun(p)).defn==nameId) {
				  hd(maPats(ma)) = arg(p);
				  goto tidyHd;
			     }
			     /* intentional fall-thru */
	    case CHARCELL  :
	    case NAME      :
	    case CONFLDS   :
			     return FALSE;

	    default        : internal("emptyMatch");
	}
    }
    return TRUE;
}

/* --------------------------------------------------------------------------
 * Discriminators:
 * ------------------------------------------------------------------------*/

static Cell local maDiscr(Cell ma)   /* Get the discriminator for a non-empty   */
{                      /* match, ma.                              */
    Cell p = hd(maPats(ma));
    Cell h = getHead(p);
    switch (whatIs(h)) {
	case CONFLDS : return fst(snd(p));
#if NPLUSK
	case ADDPAT  : arg(fun(p)) = translate(arg(fun(p)));
		       return fun(p);
#endif
#if TREX
	case EXT     : h      = fun(fun(p));
		       arg(h) = translate(arg(h));
		       return h;
#endif
	case NAME    : if (h==nameFromInt || h==nameFromInteger
					  || h==nameFromDouble) {
			   if (argCount==2)
			       arg(fun(p)) = translate(arg(fun(p)));
			   return p;
		       }
    }
    return h;
}

static Bool local isNumDiscr(Cell d) /* TRUE => numeric discriminator           */
{
    switch (whatIs(d)) {
	case NAME      :
	case TUPLE     :
	case CHARCELL  : return FALSE;

#if TREX
	case AP        : return !isExt(fun(d));
#else
	case AP        : return TRUE;   /* must be a literal or (n+k)      */
#endif
    }
    internal("isNumDiscr");
    return 0;/*NOTREACHED*/
}

Int discrArity(Cell d)                      /* Find arity of discriminator      */
{
    switch (whatIs(d)) {
	case NAME      : return name(d).arity;
	case TUPLE     : return tupleOf(d);
	case CHARCELL  : return 0;
#if TREX
	case AP        : switch (whatIs(fun(d))) {
#if NPLUSK
			     case ADDPAT : return 1;
#endif
			     case EXT    : return 2;
			     default     : return 0;
			 }
#else
#if NPLUSK
	case AP        : return (whatIs(fun(d))==ADDPAT) ? 1 : 0;
#else
	case AP        : return 0;      /* must be an Int or Double lit    */
#endif
#endif
    }
    internal("discrArity");
    return 0;/*NOTREACHED*/
}

static Bool local eqNumDiscr(Cell d1,Cell d2)     /* Determine whether two numeric   */
{                          /* descriptors have same value     */
#if NPLUSK
    if (whatIs(fun(d1))==ADDPAT)
	return whatIs(fun(d2))==ADDPAT && snd(fun(d1))==snd(fun(d2));
#endif
    if (isInt(arg(d1)))
	return isInt(arg(d2)) && intOf(arg(d1))==intOf(arg(d2));
    if (isDouble(arg(d1)))
	return isDouble(arg(d2)) && doubleOf(arg(d1))==doubleOf(arg(d2));
#if BIGNUMS
    if (isBignum(arg(d1)))
	return isBignum(arg(d2)) && bigCmp(arg(d1),arg(d2))==0;
#endif
    internal("eqNumDiscr");
    return FALSE;/*NOTREACHED*/
}

#if TREX
static Bool local isExtDiscr(Cell d)         /* Test of extension discriminator */
{
    return isAp(d) && isExt(fun(d));
}

static Bool local eqExtDiscr(Cell d1,Cell d2)     /* Determine whether two extension */
{                          /* discriminators have same label  */
    return fun(d1)==fun(d2);
}
#endif

/* --------------------------------------------------------------------------
 * Lambda Lifter:    replace local function definitions with new global
 *                   functions.  Based on Johnsson's algorithm.
 * ------------------------------------------------------------------------*/

static Cell local lift(Int co,List tr,Cell e)        /* lambda lift term                 */
{
    switch (whatIs(e)) {
	case GUARDED   : map2Proc(liftPair,co,tr,snd(e));
			 break;

	case FATBAR    : liftPair(co,tr,snd(e));
			 break;

	case CASE      : map2Proc(liftAlt,co,tr,snd(snd(e)));
			 break;

#if TREX
	case EXTCASE   :
#endif
	case NUMCASE   : liftNumcase(co,tr,snd(e));
			 break;

	case COND      : liftTriple(co,tr,snd(e));
			 break;

	case AP        : liftPair(co,tr,e);
			 break;

	case VAROPCELL :
	case VARIDCELL :
	case DICTVAR   : return liftVar(tr,e);

	case LETREC    : return liftLetrec(co,tr,e);

#if BIGNUMS
	case POSNUM    :
	case ZERONUM   :
	case NEGNUM    :
#endif
#if NPLUSK
	case ADDPAT    :
#endif
#if TREX
	case EXT       :
#endif
	case TUPLE     :
	case NAME      :
	case INTCELL   :
	case DOUBLECELL:
	case STRCELL   :
	case OFFSET    :
	case CHARCELL  : break;

	default        : internal("lift");
			 break;
    }
    return e;
}

static Void local liftPair(Int co,List tr,Pair pr)   /* lift pair of terms               */
{
    fst(pr) = lift(co,tr,fst(pr));
    snd(pr) = lift(co,tr,snd(pr));
}

static Void local liftTriple(Int co,List tr,Triple e)  /* lift triple of terms             */
{
    fst3(e) = lift(co,tr,fst3(e));
    snd3(e) = lift(co,tr,snd3(e));
    thd3(e) = lift(co,tr,thd3(e));
}

static Void local liftAlt(Int co,List tr,Cell pr)    /* lift (discr,case) pair           */
{                             /* pr :: (discr,case)               */
    snd(pr) = lift(co+discrArity(fst(pr)), tr, snd(pr));
}

static Void local liftNumcase(Int co,List tr,Triple nc)/* lift (offset,discr,case)         */
{
    Int da   = discrArity(snd3(nc));
    snd3(nc) = lift(co,tr,snd3(nc));
    thd3(nc) = lift(co+da,tr,thd3(nc));
}

static Cell local liftVar(List tr,Cell e)        /* lift variable                    */
{
    Text t = textOf(e);
    while (nonNull(tr) && textOf(fst(hd(tr)))!=t)
	tr = tl(tr);
    if (isNull(tr))
	internal("liftVar");
    return snd(hd(tr));
}

static Cell local liftLetrec(Int co,List tr,Cell e)  /* lift letrec term                 */
{
    List vs = fst(fst(snd(e)));
    List fs = snd(fst(snd(e)));
    List fds;

    co += length(vs);
    solve(fs);

    for (fds=fs; nonNull(fds); fds=tl(fds)) {
	Triple fundef = hd(fds);
	List   fvs    = fst3(thd3(fundef));
	Cell   n      = newName(textOf(fst3(fundef)),currentName);
	Cell   e0;

	for (e0=n; nonNull(fvs); fvs=tl(fvs))
	    e0 = ap(e0,hd(fvs));

	tr           = cons(pair(fst3(fundef),e0),tr);
	fst3(fundef) = n;
    }

    map2Proc(liftFundef,co,tr,fs);
    if (isNull(vs))
	return lift(co,tr,snd(snd(e)));
    map2Over(lift,co,tr,vs);
    fst(snd(e)) = vs;
    snd(snd(e)) = lift(co,tr,snd(snd(e)));
    return e;
}

static Void local liftFundef(Int co,List tr,Tripke fd) /* lift function definition         */
{
    Int arity = intOf(snd3(fd));
    newGlobalFunction(fst3(fd),                          /* name           */
		      arity,                             /* arity          */
		      fst3(thd3(fd)),                    /* free variables */
		      co+arity,                          /* current offset */
		      lift(co+arity,tr,thd3(thd3(fd)))); /* lifted case    */
    name(fst3(fd)).defn = NIL;
}

/* Each element in a list of fundefs has the form: (v,a,(fvs,ffs,rhs))
 * where fvs is a list of free variables which must be added as extra
 *           parameters to the lifted version of function v,
 *       ffs is a list of fundefs defined either in the group of definitions
 *           including v, or in some outer LETREC binding.
 *
 * In order to determine the correct value for fvs, we must include:
 * - all variables explicitly appearing in the body rhs (this much is
 *   achieved in pmcVar).
 * - all variables required for lifting those functions appearing in ffs.
 *   - If f is a fundef in an enclosing group of definitions then the
 *     correct list of variables to include with each occurrence of f will
 *     have already been calculated and stored in the fundef f.  We simply
 *     take the union of this list with fvs.
 *   - If f is a fundef in the same group of bindings as v, then we iterate
 *     to find the required solution.
 */

#if DEBUG_CODE
extern Void dumpFundefs Args((List));

Void dumpFundefs(fs)
List fs; {
    Printf("Dumping Fundefs:\n");
    for (; nonNull(fs); fs=tl(fs)) {
	Cell t   = hd(fs);
	List fvs = fst3(thd3(t));
	List ffs = snd3(thd3(t));
	Printf("Var \"%s\", arity %d:\n",textToStr(textOf(fst3(t))),
					 intOf(snd3(t)));
	Printf("Free variables: ");
	printExp(stdout,fvs);
	Putchar('\n');
	Printf("Local functions: ");
	for (; nonNull(ffs); ffs=tl(ffs)) {
	    printExp(stdout,fst3(hd(ffs)));
	    Printf("  ");
	}
	Putchar('\n');
    }
    Printf("----------------\n");
}
#endif

static Void local solve(List fs)		/* Solve eqns for lambda-lifting   */
{				/* of local function definitions   */
    Bool hasChanged;
    List fs0, fs1;

    /* initial pass distinguishes between those functions defined in fs and
     * those defined in enclosing LETREC clauses ...
     */

    for (fs0=fs; nonNull(fs0); fs0=tl(fs0)) {
	List fvs = fst3(thd3(hd(fs0)));
	List ffs = NIL;

	for (fs1=snd3(thd3(hd(fs0))); nonNull(fs1); fs1=tl(fs1)) {
	    if (cellIsMember(hd(fs1),fs))	/* function in same LETREC */
		ffs = cons(hd(fs1),ffs);
	    else {				/* enclosing letrec	   */
		List fvs1 = fst3(thd3(hd(fs1)));
		for (; nonNull(fvs1); fvs1=tl(fvs1))
		    if (!cellIsMember(hd(fvs1),fvs))
			fvs = cons(hd(fvs1),fvs);
	    }
	}
	fst3(thd3(hd(fs0))) = fvs;
	snd3(thd3(hd(fs0))) = ffs;
    }

    /* now that the ffs component of each fundef in fs has been restricted
     * to a list of fundefs in fs, we iterate to add any extra free variables
     * that are needed (in effect, calculating the reflexive transitive
     * closure of the local call graph of fs).
     */

    do {
	hasChanged = FALSE;
	for (fs0=fs; nonNull(fs0); fs0=tl(fs0)) {
	    List fvs0 = fst3(thd3(hd(fs0)));
	    for (fs1=snd3(thd3(hd(fs0))); nonNull(fs1); fs1=tl(fs1))
		 if (hd(fs1)!=hd(fs0)) {
		     List fvs1 = fst3(thd3(hd(fs1)));
		     for (; nonNull(fvs1); fvs1=tl(fvs1))
			 if (!cellIsMember(hd(fvs1),fvs0)) {
			     hasChanged = TRUE;
			     fvs0       = cons(hd(fvs1),fvs0);
			 }
		}
	    if (hasChanged) fst3(thd3(hd(fs0))) = fvs0;
	}
    } while (hasChanged);
}

/* --------------------------------------------------------------------------
 * Pre-compiler: Uses output from lambda lifter to produce terms suitable
 *               for input to code generator.
 * ------------------------------------------------------------------------*/

static List extraVars;     /* List of additional vars to add to function   */
static Int  numExtraVars;  /* Length of extraVars                          */
static Int  localOffset;   /* offset value used in original definition     */
static Int  localArity;    /* arity of function being compiled w/o extras  */

/* --------------------------------------------------------------------------
 * Arrangement of arguments on stack prior to call of
 *                 n x_1 ... x_e y_1 ... y_a
 * where
 *      e = numExtraVars,      x_1,...,x_e are the extra params to n
 *      a = localArity of n,   y_1,...,y_a are the original params
 *
 *    offset 1     :  y_a  }                           STACKPART1
 *      ..                 }
 *    offset a     :  y_1  }
 *
 *    offset 1+a   :  x_e  }                           STACKPART2
 *      ..                 }
 *    offset e+a   :  x_1  }
 *
 *    offset e+a+1 :  used for temporary results ...   STACKPART3
 *      ..
 *      ..
 *
 * In the original defn for n, the offsets in STACKPART1 and STACKPART3
 * are contiguous.  To add the extra parameters we need to insert the
 * offsets in STACKPART2, adjusting offset values as necessary.
 * ------------------------------------------------------------------------*/

static Cell local preComp(Cell e)		/* Adjust output from compiler to  */
{				/* include extra parameters	   */
    switch (whatIs(e)) {
	case GUARDED   : mapOver(preCompPair,snd(e));
			 break;

	case LETREC    : mapOver(preComp,fst(snd(e)));
			 snd(snd(e)) = preComp(snd(snd(e)));
			 break;

	case COND      : return ap(COND,preCompTriple(snd(e)));

	case FATBAR    : return ap(FATBAR,preCompPair(snd(e)));

	case AP        : return preCompPair(e);

	case CASE      : fst(snd(e)) = preComp(fst(snd(e)));
			 mapProc(preCompCase,snd(snd(e)));
			 break;

#if TREX
	case EXTCASE   : return ap(EXTCASE,preCompTriple(snd(e)));
#endif

	case NUMCASE   : return ap(NUMCASE,preCompTriple(snd(e)));

	case OFFSET    : return preCompOffset(offsetOf(e));

#if BIGNUMS
	case POSNUM    :
	case ZERONUM   :
	case NEGNUM    :
#endif
#if NPLUSK
	case ADDPAT    :
#endif
#if TREX
	case EXT       :
#endif
	case TUPLE     :
	case NAME      :
	case INTCELL   :
	case DOUBLECELL:
	case STRCELL   :
	case CHARCELL  : break;

	default        : internal("preComp");
    }
    return e;
}

static Cell local preCompPair(Pair e)       /* Apply preComp to pair of Exprs   */
{
    return pair(preComp(fst(e)),
		preComp(snd(e)));
}

static Cell local preCompTriple(Triple e)     /* Apply preComp to triple of Exprs */
{
    return triple(preComp(fst3(e)),
		  preComp(snd3(e)),
		  preComp(thd3(e)));
}

static Void local preCompCase(Pair e)       /* Apply preComp to (Discr,Expr)    */
{
    snd(e) = preComp(snd(e));
}

static Cell local preCompOffset(Int n)	/* Determine correct offset value  */
{				/* for local variable/function arg.*/
    if (n>localOffset-localArity)
	if (n>localOffset)				    /* STACKPART3  */
	    return mkOffset(n-localOffset+localArity+numExtraVars);
	else						    /* STACKPART1  */
	    return mkOffset(n-localOffset+localArity);
    else {						    /* STACKPART2  */
	List fvs = extraVars;
	Int  i   = localArity+numExtraVars;

	for (; nonNull(fvs) && offsetOf(hd(fvs))!=n; --i)
	    fvs=tl(fvs);
	return mkOffset(i);
    }
}

/* --------------------------------------------------------------------------
 * Main entry points to compiler:
 * ------------------------------------------------------------------------*/

Void compileExp() {			/* compile input expression	   */
    compiler(RESET);

    currentName  = NIL;
    inputExpr    = lift(0,NIL,pmcTerm(0,NIL,translate(inputExpr)));
    extraVars    = NIL;
    numExtraVars = 0;
    localOffset  = 0;
    localArity   = 0;
    inputExpr    = preComp(inputExpr);
#if DEBUG_SHOWSC
    if (debugSC)
	printSc(stdout,findText("main"),0,inputExpr);
#endif
    inputCode    = codeGen(NIL,0,inputExpr);
    inputExpr    = NIL;
}


Void compileDefns() {			/* compile script definitions	   */
    Target t = length(valDefns) + length(genDefns) + length(selDefns);
    Target i = 0;

#if DEBUG_SHOWSC
    Module mod;
    String modName;
    char name[256];
    List dataCons = NIL;

    if (debugSC) {
      mod = currentModule;
      modName = textToStr(module(currentModule).text);
      if (snprintf(name,sizeof(name)-1, "%s.cor", modName) < 0) {
	  ERRMSG(0) "Module name (%s) too long", modName
          EEND_NORET;
      } else {
	  name[sizeof(name)-1] = '\0';
	  scfp = fopen(name,"w");
	  fprintf(scfp,"module %s;\n",modName);
	  dataCons = dupOnto(dataCons,module(currentModule).tycons);
	  dataCons = dupOnto(dataCons,module(currentModule).classes);
	  for (; nonNull(dataCons); dataCons=tl(dataCons)) {
	      Cell t = hd(dataCons);
	      switch(whatIs(t)) {
	      case TYCON:
		  if (tycon(t).what == DATATYPE
		      && nonNull(tycon(t).defn)
		      && tycon(t).mod == mod) {
		      fprintf(scfp,"data %s",
			      textToStr(tycon(t).text));
		      debugConstructors(scfp,tycon(t).defn);
		      fprintf(scfp,";\n");
		  }
		  break;
	      case CLASS:
		  if (cclass(t).mod == mod) {
		      fprintf(scfp,"data %s = ",
			      textToStr(cclass(t).text));
		      debugConstructor(scfp,cclass(t).dcon);
		      fprintf(scfp,";\n");
		  }
		  break;
	      default:
		  fprintf(scfp,"** unknown datacons **");
	      }
	  }
      }
    }
#endif

    setGoal("Compiling",t);

    for (; nonNull(valDefns); valDefns=tl(valDefns)) {
	hd(valDefns) = transBinds(hd(valDefns));
	mapProc(compileGlobalFunction,hd(valDefns));
	soFar(i++);
    }
    for (; nonNull(genDefns); genDefns=tl(genDefns)) {
	compileGenFunction(hd(genDefns));
	soFar(i++);
    }
    for (; nonNull(selDefns); selDefns=tl(selDefns)) {
	mapOver(compileSelFunction,hd(selDefns));
	soFar(i++);
    }

#if DEBUG_SHOWSC
    if (debugSC) {
      fprintf(scfp,"\n-- end of module %s --\n",modName);
      fclose(scfp);
    }
#endif

    done();
}

#if DEBUG_SHOWSC
static Void local debugConstructors(FILE *fp,Cell c) {
  char ch = '=';
  while(isAp(c)) {
    if (whatIs(hd(c)) == NAME) {
      fprintf(fp,"\n %c ",ch);
      ch = '|';
      debugConstructor(fp,hd(c));
    }
    c = tl(c);
  }
}

static Void local debugConstructor(FILE *fp,Name c) {
  int i;
  switch(whatIs(c)) {
  case NAME: 
    fprintf(fp,"%s",textToStr(name(c).text));
    for(i=0;i < name(c).arity;i++) {
      fprintf(scfp," *");
    }
    break;
  default:
    fprintf(fp,"** unknown constructor **");
  }
}
#endif

static Void local compileGlobalFunction(Pair bind)
{
    Name n     = findName(textOf(fst(bind)));
    List defs  = snd(bind);
    Int  arity = length(fst(hd(defs)));

    if (isNull(n))
	internal("compileGlobalFunction");
    compiler(RESET);
    currentName  = n;
    defs = altsMatch(1,arity,NIL,defs);
    newGlobalFunction(n,arity,NIL,arity,lift(arity,NIL,match(arity,defs)));
    name(n).defn = NIL;
}

static Void local compileGenFunction(Name n)	/* Produce code for internally	   */
{				/* generated function		   */
    List defs  = name(n).defn;
    Int  arity = length(fst(hd(defs)));

    compiler(RESET);
    currentName = n;
    mapProc(transAlt,defs);
    defs = altsMatch(1,arity,NIL,defs);
    newGlobalFunction(n,arity,NIL,arity,lift(arity,NIL,match(arity,defs)));
    name(n).defn = NIL;
}

static Name local compileSelFunction(Pair p) /* Produce code for selector func  */
{				/* Should be merged with genDefns, */
    Name s     = fst(p);		/* but the name(_).defn field is   */
    List defs  = snd(p);		/* already used for other purposes */
    Int  arity = length(fst(hd(defs))); /* in selector functions.	   */

    compiler(RESET);
    mapProc(transAlt,defs);
    defs = altsMatch(1,arity,NIL,defs);
    newGlobalFunction(s,arity,NIL,arity,lift(arity,NIL,match(arity,defs)));
    return s;
}

static Void local newGlobalFunction(Name n,Int arity,List fvs,Int co,Cell e)
{
    extraVars     = fvs;
    numExtraVars  = length(extraVars);
    localOffset   = co;
    localArity    = arity;
    name(n).arity = arity+numExtraVars;
    e             = preComp(e);
#if DEBUG_SHOWSC
    if (debugSC) {
	printSc(scfp,name(n).text,name(n).arity,e);
    }
#endif
    name(n).code  = codeGen(n,name(n).arity,e);
}

/* --------------------------------------------------------------------------
 * Compiler control:
 * ------------------------------------------------------------------------*/

Void compiler(Int what)
{
    switch (what) {
	case INSTALL :
	case RESET   : freeVars      = NIL;
		       freeFuns      = NIL;
		       freeBegin     = mkOffset(0);
		       extraVars     = NIL;
		       numExtraVars  = 0;
		       localOffset   = 0;
		       localArity    = 0;
		       break;

	case MARK    : mark(freeVars);
		       mark(freeFuns);
		       mark(extraVars);
		       break;
    }
}

/*-------------------------------------------------------------------------*/

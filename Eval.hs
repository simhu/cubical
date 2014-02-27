module Eval ( evalTer
            , evalTers
            , appVal
            , convVal
            , fstSVal
            ) where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
-- nIso breaks if we use:
-- import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import Data.List
import Data.Maybe (fromMaybe)

import CTT

type Eval a = StateT Trace Identity a

runEval :: Eval a -> (a,Trace)
runEval e = runIdentity $ runStateT e []

evalTer :: Env -> Ter -> (Val,Trace)
evalTer env = runEval . eval env

evalTers :: Env -> [(Binder,Ter)] -> ([(Binder,Val)],Trace)
evalTers env bts = runEval (evals env bts)

appVal :: Val -> Val -> (Val,Trace)
appVal v1 v2 = runEval $ app v1 v2

convVal :: Int -> Val -> Val -> (Bool,Trace)
convVal k v1 v2 = runEval $ conv k v1 v2

trace :: String -> Eval ()
trace s = modify (\x -> x ++ [s])

look :: Binder -> Env -> Val
look x (Pair s (y,u)) | x == y    = u
                      | otherwise = look x s
look x r@(PDef es r1)             = case lookup x es of
  Just t  -> fst $ evalTer r t
  Nothing -> look x r1

eval :: Env -> Ter -> Eval Val
eval e U                 = return VU
eval e (PN pn)           = evalAppPN e pn []
eval e t@(App r s)       = case unApps t of
  (PN pn,us) -> evalAppPN e pn us
  _          -> appM (eval e r) (eval e s)
eval e (Var i)           = return $ look i e
eval e (Pi a b)          = VPi <$> eval e a <*> eval e b
eval e (Lam x t)         = return $ Ter (Lam x t) e -- stop at lambdas
eval e (Sigma a b)       = VSigma <$> eval e a <*> eval e b
eval e (SPair a b)       = VSPair <$> eval e a <*> eval e b
eval e (Fst a)           = fstSVal <$> eval e a
eval e (Snd a)           = sndSVal <$> eval e a
eval e (Where t (_,def)) = eval (PDef def e) t
eval e (Con name ts)     = VCon name <$> mapM (eval e) ts
eval e (Split pr alts)   = return $ Ter (Split pr alts) e
eval e (Sum pr ntss)     = return $ Ter (Sum pr ntss) e

evals :: Env -> [(Binder,Ter)] -> Eval [(Binder,Val)]
evals env = sequenceSnd . map (second (eval env))

fstSVal, sndSVal :: Val -> Val
fstSVal (VSPair a b)    = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal (VSPair a b)    = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"

-- Application
app :: Val -> Val -> Eval Val
app (Ter (Lam x t) e) u                         = eval (Pair e (x,u)) t
app (Kan Com (VPi a b) box@(Box dir x v nvs)) u = do
  trace "Pi Com"
  ufill <- fill a (Box (mirror dir) x u [])
  bcu   <- cubeToBox ufill (shapeOfBox box)
  comM (app b ufill) (appBox box bcu)
app kf@(Kan Fill (VPi a b) box@(Box dir i w nws)) v = do
  trace "Pi fill"
  let x = fresh (kf, v)
  u     <- v `face` (i,dir)
  ufill <- fill a (Box (mirror dir) i u [])
  bcu   <- cubeToBox ufill (shapeOfBox box)
  vfill <- fill a (Box (mirror dir) i u [((x,down),ufill),((x,up),v)])
  vx    <- fillM (app b ufill) (appBox box bcu)
  vi0   <- appM (return w) (vfill `face` (i,down))
  vi1   <- comM (app b ufill) (appBox box bcu)
  nvs   <- sequenceSnd [ ((n,d),appM (return ws) (vfill `face` (n,d)))
                       | ((n,d),ws) <- nws ]
  comM (app b vfill) (return (Box up x vx (((i,down),vi0) : ((i,up),vi1):nvs)))
app vext@(VExt x bv fv gv pv) w = do
  -- NB: there are various choices how to construct this
  let y = fresh (vext, w)
  w0    <- w `face` (x,down)
  left  <- app fv w0
  right <- app gv (swap w x y)
  pvxw  <- appNameM (app pv w0) x
  comM (app bv w) (return (Box up y pvxw [((x,down),left),((x,up),right)]))
app (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t)  -> eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name
app u@(Ter (Split _ _) _) v
  | isNeutral v = return $ VSplit u v -- v should be neutral
  | otherwise   = error $ "app: (VSplit) " ++ show v ++ " is not neutral"
app r s
  | isNeutral r = return $ VApp r s -- r should be neutral
  | otherwise   = error $ "app: (VApp) " ++ show r ++ " is not neutral"

-- Monadic version of app
appM :: Eval Val -> Eval Val -> Eval Val
appM t1 t2 = do
  u <- t1
  v <- t2
  app u v

apps :: Val -> [Val] -> Eval Val
apps = foldM app

appBox :: Box Val -> Box Val -> Eval (Box Val)
appBox (Box dir x v nvs) (Box _ _ u nus) = do
  let lookup' x = fromMaybe (error "appBox") . lookup x
  sequenceBox $ Box dir x (app v u) [ (nnd,app v (lookup' nnd nus))
                                    | (nnd,v) <- nvs ]

appName :: Val -> Name -> Eval Val
appName (Path x u) y | y `elem` [0,1] = u `face` (x,y)
appName p y          | y `elem` [0,1] = return $ VAppName p y
                                        -- p has to be neutral
appName (Path x u) y | x == y             = return u
                     | y `elem` support u = error ("appName " ++ "\nu = " ++
                                                   show u ++ "\ny = " ++ show y)
                     | otherwise          = return $ swap u x y
appName v y          = return $ VAppName v y

appNameM :: Eval Val -> Name -> Eval Val
appNameM v n = do
  v' <- v
  appName v' n

-- Apply a primitive notion
evalAppPN :: Env -> PN -> [Ter] -> Eval Val
evalAppPN e pn ts
  | length ts < arity pn =
      -- Eta expand primitive notions
      let r       = arity pn - length ts
          binders = map (\n -> '_' : show n) [1..r]
          vars    = map Var binders
      in return $ Ter (mkLams binders $ mkApps (PN pn) (ts ++ vars)) e
  | otherwise = do
      let (args,rest) = splitAt (arity pn) ts
      vas <- mapM (eval e) args
      p   <- evalPN (freshs e) pn vas
      r   <- mapM (eval e) rest
      apps p r

-- Evaluate primitive notions
evalPN :: [Name] -> PN -> [Val] -> Eval Val
evalPN (x:_) Id            [a,a0,a1]     = return $ VId (Path x a) a0 a1
evalPN (x:_) IdP           [_,_,p,a0,a1] = return $ VId p a0 a1
evalPN (x:_) Refl          [_,a]         = return $ Path x a
evalPN (x:_) TransU        [_,_,p,t]     =
  comM (appName p x) (return (Box up x t []))
evalPN (x:_) TransInvU     [_,_,p,t]     =
  comM (appName p x) (return (Box down x t []))
evalPN (x:_) TransURef     [a,t]         = Path x <$> fill a (Box up x t [])
evalPN (x:_) TransUEquivEq [_,b,f,_,_,u] = do
  fu <- app f u
  Path x <$> fill b (Box up x fu [])   -- TODO: Check this!
evalPN (x:y:_) CSingl [a,u,v,p] = do
  pv    <- appName p y
  theta <- fill a (Box up y u [((x,down),u),((x,up),pv)])
  omega <- theta `face` (y,up)
  return $ Path x (VSPair omega (Path y theta))
evalPN (x:_)   Ext        [_,b,f,g,p]   = return $ Path x $ VExt x b f g p
evalPN _       Inh        [a]           = return $ VInh a
evalPN _       Inc        [_,t]         = return $ VInc t
evalPN (x:_)   Squash     [_,r,s]       = return $ Path x $ VSquash x r s
evalPN _       InhRec     [_,b,p,phi,a] = inhrec b p phi a
evalPN (x:_)   EquivEq    [a,b,f,s,t]   = return $ Path x $ VEquivEq x a b f s t
evalPN (x:y:_) EquivEqRef [a,s,t]       =
  return $ Path y $ Path x $ VEquivSquare x y a s t
evalPN (x:_)   MapOnPath  [_,_,f,_,_,p]    =
  Path x <$> appM (return f) (appName p x)
evalPN (x:_)   MapOnPathD [_,_,f,_,_,p]    =
  Path x <$> appM (return f) (appName p x)
evalPN (x:_)   AppOnPath [_,_,_,_,_,_,p,q] =
  Path x <$> appM (appName p x) (appName q x)
evalPN (x:_)   MapOnPathS [_,_,_,f,_,_,p,_,_,q] =
  Path x <$> appM (appM (pure f) (appName p x)) (appName q x)
evalPN _       Circle     []               = return VCircle
evalPN _       Base       []               = return VBase
evalPN (x:_)   Loop       []               = return $ Path x $ VLoop x
evalPN _       CircleRec  [f,b,l,s]        = circlerec f b l s
evalPN _       I          []               = return VI
evalPN _       I0         []               = return VI0
evalPN _       I1         []               = return VI1
evalPN (x:_)   Line       []               = return $ Path x $ VLine x
evalPN _       IntRec     [f,s,e,l,u]      = intrec f s e l u
evalPN _       u          _                = error ("evalPN " ++ show u)

-- Compute the face of an environment
faceEnv :: Env -> Side -> Eval Env
faceEnv e xd = mapEnvM (`face` xd) e

faceName :: Name -> Side -> Name
faceName 0 _                 = 0
faceName 1 _                 = 1
faceName x (y,d) | x == y    = d
                 | otherwise = x

-- Compute the face of a value
face :: Val -> Side -> Eval Val
face u xdir@(x,dir) =
  let fc v = v `face` xdir in case u of
  VU          -> return VU
  Ter t e -> do e' <- e `faceEnv` xdir
                eval e' t
  VId a v0 v1 -> VId <$> fc a <*> fc v0 <*> fc v1
  Path y v | x == y    -> return u
           | otherwise -> Path y <$> fc v
  VExt y b f g p | x == y && dir == down -> return f
                 | x == y && dir == up   -> return g
                 | otherwise             ->
                   VExt y <$> fc b <*> fc f <*> fc g <*> fc p
  VPi a f    -> VPi <$> fc a <*> fc f
  VSigma a f -> VSigma <$> fc a <*> fc f
  VSPair a b -> VSPair <$> fc a <*> fc b
  VInh v     -> VInh <$> fc v
  VInc v     -> VInc <$> fc v
  VSquash y v0 v1 | x == y && dir == down -> return v0
                  | x == y && dir == up   -> return v1
                  | otherwise             -> VSquash y <$> fc v0 <*> fc v1
  VCon c us -> VCon c <$> mapM fc us
  VEquivEq y a b f s t | x == y && dir == down -> return a
                       | x == y && dir == up   -> return b
                       | otherwise             ->
                         VEquivEq y <$> fc a <*> fc b <*> fc f <*> fc s <*> fc t
  VPair y a v | x == y && dir == down -> return a
              | x == y && dir == up   -> fc v
              | otherwise             -> VPair y <$> fc a <*> fc v
  VEquivSquare y z a s t | x == y                -> return a
                         | x == z && dir == down -> return a
                         | x == z && dir == up   -> do
                           let idV = Ter (Lam "x" (Var "x")) Empty
                           return $ VEquivEq y a a idV s t
                         | otherwise             ->
                          VEquivSquare y z <$> fc a <*> fc s <*> fc t
  VSquare y z v | x == y                -> fc v
                | x == z && dir == down -> fc v
                | x == z && dir == up   -> do
                  v' <- fc v
                  VPair y <$> v' `face` (y,down) <*> pure v'
                | otherwise             -> VSquare y z <$> fc v
  Kan Fill a b@(Box dir' y v nvs)
    | x /= y && x `notElem` nonPrincipal b -> fillM (fc a) (mapBoxM fc b)
    | x `elem` nonPrincipal b              -> return $ lookBox (x,dir) b
    | x == y && dir == mirror dir'         -> return v
    | otherwise                            -> com a b
  VFillN a b@(Box dir' y v nvs)
    | x /= y && x `notElem` nonPrincipal b -> fillM (fc a) (mapBoxM fc b)
    | x `elem` nonPrincipal b              -> return $ lookBox (x,dir) b
    | x == y && dir == mirror dir'         -> return v
    | otherwise                            -> com a b
  Kan Com a b@(Box dir' y v nvs)
    | x == y                     -> return u
    | x `notElem` nonPrincipal b -> comM (fc a) (mapBoxM fc b)
    | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
  VComN a b@(Box dir' y v nvs)
    | x == y                     -> return u
    | x `notElem` nonPrincipal b -> comM (fc a) (mapBoxM fc b)
    | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
  VComp b@(Box dir' y _ _)
    | x == y                     -> return u
    | x `notElem` nonPrincipal b -> VComp <$> mapBoxM fc b
    | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
  VFill z b@(Box dir' y v nvs)
    | x == z                               -> return u
    | x /= y && x `notElem` nonPrincipal b -> VFill z <$> mapBoxM fc b
    | (x,dir) `elem` defBox b              ->
      lookBox (x,dir) <$> mapBoxM (`face` (z,down)) b
    | x == y && dir == dir'                ->
        VComp <$> mapBoxM (`face` (z,up)) b
  -- TODO: Is it ok to use join here?
  VInhRec b p h a     -> join $ inhrec <$> fc b <*> fc p <*> fc h <*> fc a
  VApp u v            -> appM (fc u) (fc v)
  VAppName u n        -> do
   trace ("face " ++ "\nxdir " ++ show xdir ++
          "\nu " ++ show u ++ "\nn " ++ show n)
   appNameM (fc u) (faceName n xdir)
  VSplit u v          -> appM (fc u) (fc v)
  VVar s d            -> return $ VVar s [ faceName n xdir | n <- d ]
  VFst p              -> fstSVal <$> fc p
  VSnd p              -> sndSVal <$> fc p
  VCircle             -> return VCircle
  VBase               -> return VBase
  VLoop y | x == y    -> return VBase
          | otherwise -> return $ VLoop y
  VCircleRec f b l s  -> join $ circlerec <$> fc f <*> fc b <*> fc l <*> fc s
  VI  -> return VI
  VI0 -> return VI0
  VI1 -> return VI1
  VLine y
    | x == y && dir == down -> return VI0
    | x == y && dir == up   -> return VI1
    | otherwise             -> return $ VLine y
  VIntRec f s e l u -> join $ intrec <$> fc f <*> fc s <*> fc e <*> fc l <*> fc u

faceM :: Eval Val -> Side -> Eval Val
faceM t xdir = do
  v <- t
  v `face` xdir

unCompAs :: Val -> Name -> Box Val
unCompAs (VComp box) y = swap box (pname box) y
unCompAs v           _ = error $ "unCompAs: " ++ show v ++ " is not a VComp"

unFillAs :: Val -> Name -> Box Val
unFillAs (VFill x box) y = swap box x y
unFillAs v             _ = error $ "unFillAs: " ++ show v ++ " is not a VFill"

-- p(x) = <z>q(x,z)
-- a(x) = q(x,0)     b(x) = q(x,1)
-- q(0,y) connects a(0) and b(0)
-- we connect q(0,0) to q(1,1)
-- appDiag :: Val -> Val -> Name -> Val
-- appDiag tu p x | x `elem` [0,1] = appName p x
-- appDiag tu p x =
-- traceb ("appDiag " ++ "\ntu = " ++ show tu ++ "\np = " ++ show p ++ "\nx = "
-- --                       ++ show x ++ " " ++ show y
-- --                       ++ "\nq = " ++ show q) -- "\nnewBox =" ++ show newBox)
--  com tu newBox
--    where y = fresh (p,(tu,x))
--          q = appName p y
--          a = appName p 0
--          b = appName p 1
--          newBox = Box down y b [((x,down),q `face` (x,down)),((x,up),b `face` (x,up))]

cubeToBox :: Val -> Box () -> Eval (Box Val)
cubeToBox v = modBoxM (\nd _ -> v `face` nd)

inhrec :: Val -> Val -> Val -> Val -> Eval Val
inhrec _ _ phi (VInc a)          = app phi a
inhrec b p phi (VSquash x a0 a1) = do
  let fc w d = w `face` (x,d)
  b0 <- join $ inhrec <$> fc b down <*> fc p down <*> fc phi down <*> pure a0
  b1 <- join $ inhrec <$> fc b up   <*> fc p up   <*> fc phi up   <*> pure a1
  appNameM (appM (app p b0) (return b1) `faceM` (x,down)) x
  -- appDiag b (app (app p b0) b1) x  -- x may occur in p and/or b
inhrec b p phi (Kan ktype (VInh a) box) = do
  let irec (j,dir) v = let fc v = v `face` (j,dir)
                       in join $ inhrec <$> fc b <*> fc p <*> fc phi <*> pure v
  box' <- modBoxM irec box
  kan ktype b box'
inhrec b p phi v = return $ VInhRec b p phi v -- v should be neutral

circlerec :: Val -> Val -> Val -> Val -> Eval Val
circlerec _ b _ VBase       = return b
circlerec f b l v@(VLoop x) = do
  let y = fresh [f,b,l,v]
  pxy   <- appName l y
  theta <- connection VCircle x y v
  a     <- app f theta
  px1   <- pxy `face` (y,up)
  p11   <- px1 `face` (x,up)
  p0y   <- pxy `face` (x,down)
  trace ("circlerec " ++ "\nf = " ++ show f ++ "\nl = " ++
         show l ++ "\nx = " ++ show x)
  com a (Box down y px1 [((x,down),p0y),((x,up),p11)])
circlerec f b l v@(Kan ktype VCircle box) = do
  let crec side u = let fc w = w `face` side
                    in join $ circlerec <$> fc f <*> fc b <*> fc l <*> pure u
  fv   <- app f v
  box' <- modBoxM crec box
  kan ktype fv box'
circlerec f b l v = return $ VCircleRec f b l v -- v should be neutral

-- Assumes y is fresh and x fresh for a; constructs a connection
-- square with faces u (x), u (y), u (1), u (1).
connection :: Val -> Name -> Name -> Val -> Eval Val
connection a x y u = do
  u1    <- u `face` (x,up)
  ufill <- fill a (Box down y u1 [((x,down), swap u x y), ((x,up),u1)])
  let z       = fresh ([x,y], [a,u])
      ufillzy = swap ufill x z
      ufillzx = swap ufillzy y x
  com a (Box down z u1 [ ((x,down),ufillzy), ((x,up),u1)
                       , ((y,down),ufillzx), ((y,up),u1)])

intrec :: Val -> Val -> Val -> Val -> Val -> Eval Val
intrec _ s _ _ VI0         = return s
intrec _ _ e _ VI1         = return e
intrec f s e l v@(VLine x) = do
  let y = fresh [f,s,e,l,v]
  pxy   <- appName l y
  theta <- connection VI x y v
  a     <- app f theta
  px1   <- pxy `face` (y,up)
  p11   <- px1 `face` (x,up)
  p0y   <- pxy `face` (x,down)
  com a (Box down y px1 [((x,down),p0y),((x,up),p11)])
intrec f s e l v@(Kan ktype VCircle box) = do
  let irec side u = let fc w = w `face` side
                    in join $ intrec <$> fc f <*> fc s <*>
                                         fc e <*> fc l <*> pure u
  fv   <- app f v
  box' <- modBoxM irec box
  kan ktype fv box'
intrec f s e l v = return $ VIntRec f s e l v -- v should be neutral

kan :: KanType -> Val -> Box Val -> Eval Val
kan Fill = fill
kan Com  = com

isNeutralFill :: Val -> Box Val -> Eval Bool
isNeutralFill v box | isNeutral v               = return True
isNeutralFill v@(Ter (PN (Undef _)) _) box      = return True
isNeutralFill (Ter (Sum _ _) _) (Box _ _ v nvs) =
 return $ isNeutral v || or [ isNeutral u | (_,u) <- nvs ]
isNeutralFill v@(Kan Com VU tbox') box@(Box d x _ _) = do
  let nK  = nonPrincipal tbox'
      nJ  = nonPrincipal box
      nL  = nJ \\ nK
      aDs = if x `elem` nK then allDirs nL else (x,mirror d):allDirs nL
  return $ or [ isNeutral (lookBox yc box) | yc <- aDs ]
isNeutralFill v@(Kan Fill VU tbox') box@(Box d x _ _) = do
  let nK  = pname tbox' : nonPrincipal tbox'
      nJ  = nonPrincipal box
      nL  = nJ \\ nK
      aDs = if x `elem` nK then allDirs nL else (x,mirror d):allDirs nL
  return $ or [ isNeutral (lookBox yc box) | yc <- aDs ]
isNeutralFill v@(VEquivSquare y z _ _ _) box@(Box d x _ _) = do
  let nJ  = nonPrincipal box
      nL  = nJ \\ [y,z]
      aDs = if x `elem` [y,z] then allDirs nL else (x,mirror d):allDirs nL
  return $ or [ isNeutral (lookBox yc box) | yc <- aDs ]
isNeutralFill v@(VEquivEq z a b f s t) box@(Box d x vx nxs) = do
  -- This is the only monadic case as we use app...
  b <- isNeutral <$> app s vx
  if b && z == x && d == down
     then return True
     else do -- TODO: check
             let nJ  = nonPrincipal box
                 nL  = nJ \\ [z]
                 aDs = if x == z then allDirs nL else (x,mirror d):allDirs nL
             return $ or [ isNeutral (lookBox yc box) | yc <- aDs ]
isNeutralFill v box = return False

-- Monadic version of fill
fillM :: Eval Val -> Eval (Box Val) -> Eval Val
fillM v b = do
  v' <- v
  b' <- b
  fill v' b'

fills :: [(Binder,Ter)] -> Env -> [Box Val] -> Eval [Val]
fills []         _ []          = return []
fills ((x,a):as) e (box:boxes) = do
  v  <- fillM (eval e a) (return box)
  vs <- fills as (Pair e (x,v)) boxes
  return $ v : vs
fills _ _ _ = error "fills: different lengths of types and values"

unPack :: Name -> Name -> (Name,Dir) -> Val -> Val
unPack x y (z,c) v | z /= x && z /= y  = unSquare v
                   | z == y && c == up = sndVal v
                   | otherwise         = v

-- Kan filling
fill :: Val -> Box Val -> Eval Val
-- TODO: is is ok to use runEval like this?
fill v box | fst (runEval (isNeutralFill v box)) = return $ VFillN v box
fill vid@(VId a v0 v1) box@(Box dir i v nvs) = do
  let x = fresh (vid, box)
  box' <- consBox (x,(v0,v1)) <$> mapBoxM (`appName` x) box
  Path x <$> fillM (a `appName` x) (return box')
fill (VSigma a f) box@(Box dir x v nvs) = do
  u <- fill a (mapBox fstSVal box)
  VSPair u <$> fillM (app f u) (return (mapBox sndSVal box))
-- assumes cvs are constructor vals
fill v@(Ter (Sum _ nass) env) box@(Box _ _ (VCon n _) _) = case lookup n nass of
  Just as -> do
    let boxes = transposeBox $ mapBox unCon box
    -- fill boxes for each argument position of the constructor
    VCon n <$> fills as env boxes
  Nothing -> error $ "fill: missing constructor in labelled sum " ++ n
fill (VEquivSquare x y a s t) box@(Box dir x' vx' nvs) =
  VSquare x y <$> fill a (modBox (unPack x y) box)
fill veq@(VEquivEq x a b f s t) box@(Box dir z vz nvs)
  | x /= z && x `notElem` nonPrincipal box = do
    trace "VEquivEq case 1"
    ax0 <- fill a (mapBox fstVal box)
    bx0 <- app f ax0
    let bx = mapBox sndVal box
    bx' <- mapBoxM (`face` (x,up)) bx
    bx1 <- fill b bx'        --- independent of x
    v   <- fill b $ (x,(bx0,bx1)) `consBox` bx
    return $ VPair x ax0 v
  | x /= z && x `elem` nonPrincipal box = do
    trace "VEquivEq case 2"
    let ax0 = lookBox (x,down) box

        -- modification function
        mf (ny,dy) vy | x /= ny    = return (sndVal vy)
                      | dy == down = app f ax0
                      | otherwise  = return vy

    bx  <- sequenceBox $ modBox mf box
    VPair x ax0 <$> fill b bx
  | x == z && dir == up = do
    trace "VEquivEq case 3"
    let ax0 = vz
    bx0 <- app f ax0
    v   <- fill b $ Box dir z bx0 [ (nnd,sndVal v) | (nnd,v) <- nvs ]
    return $ VPair x ax0 v
  | x == z && dir == down = do
    trace "VEquivEq case 4"
    gbsb <- app s vz
    let (gb,sb) = (fstSVal gbsb, sndSVal gbsb)
        y       = fresh (veq, box)
    vy <- appName sb x

    let vpTSq :: Name -> Dir -> Val -> Eval (Val,Val)
        vpTSq nz dz (VPair z a0 v0) = do
          let vp = VSPair a0 (Path z v0)
          t0 <- t `face` (nz,dz)
          b0 <- vz `face` (nz,dz)
          l0sq0 <- appNameM (appM (app t0 b0) (return vp)) y
          let (l0,sq0) = (fstSVal l0sq0, sndSVal l0sq0)
          sq0x <- appName sq0 x
          return (l0,sq0x)  -- TODO: check the correctness of the square s0

    -- TODO: Use modBox!
    vsqs <- sequenceSnd [ ((n,d),vpTSq n d v) | ((n,d),v) <- nvs]
    let box1   = Box up y gb [ (nnd,v) | (nnd,(v,_)) <- vsqs ]
    afill <- fill a box1

    acom <- afill `face` (y,up)
    fafill <- app f afill

    let box2 = Box up y vy (((x,down),fafill) : ((x,up),vz) :
                            [ (nnd,v) | (nnd,(_,v)) <- vsqs ])
    bcom <- com b box2
    return $ VPair x acom bcom
  | otherwise = error "fill EqEquiv"
fill v@(Kan Com VU tbox') box@(Box dir x' vx' nvs')
  | toAdd /= [] = do  -- W.l.o.g. assume that box contains faces for
                      -- the non-principal sides of tbox.

    trace "Kan Com 1"

    let -- TODO: Is this correct? Do we have to consider the auxsides?
        add :: Side -> Eval Val
        add yc = do box' <- mapBoxM (`face` yc) box
                    fillM (lookBox yc tbox `face` (x,tdir)) (return box')

    -- Note: This could be done nicer by providing a monad instance for (,)
    sides' <- sequence [ do m1 <- add (n,down)
                            m2 <- add (n,up)
                            return (n,(m1,m2)) | n <- toAdd ]

    fill v (sides' `appendBox` box)
  | x' `notElem` nK = do
    trace "Kan Com 2"

    principal <- fill tx (mapBox (pickout (x,tdir')) boxL)
    nonprincipal <-
      sequence [ do pyc <- principal `face` yc
                    let side = [((x,tdir),lookBox yc box),((x,tdir'),pyc)]
                    v' <- fill (lookBox yc tbox)
                               (side `appendSides` mapBox (pickout yc) boxL)
                    return (yc,v')
               | yc <- allDirs nK ]

    return $ VComp (Box tdir x principal nonprincipal)
  | x' `elem` nK = do
    trace "Kan Com 3"

    let -- assumes zc in defBox tbox
        auxsides zc = [ (yd,pickout zc (lookBox yd box)) | yd <- allDirs nL ]

    -- extend input box along x with orientation tdir'; results
    -- in the non-principal faces on the intersection of defBox
    -- box and defBox tbox; note, that the intersection contains
    -- (x',dir'), but not (x',dir) (and (x,_))
    npintbox <- modBoxM (\yc boxside -> fill (lookBox yc tbox)
                                             (Box tdir' x boxside (auxsides yc)))
                        (subBox (nK `intersect` nJ) box)

    npintfacebox <- mapBoxM (`face` (x,tdir')) npintbox
    principal    <- fill tx (auxsides (x,tdir') `appendSides` npintfacebox)
    nplp         <- principal `face` (x',dir)
    fnpintboxs   <- sequence [ do fv <- v `face` (x',dir)
                                  return (yc,fv)
                             | (yc,v) <- sides npintbox ]

    let nplnp = auxsides (x',dir) ++ fnpintboxs
    -- the missing non-principal face on side (x',dir)
    v' <- fill (lookBox (x',dir) tbox) (Box tdir x nplp nplnp)
    let nplast = ((x',dir),v')

    return $ VComp (Box tdir x principal (nplast:fromBox npintbox))
  where nK    = nonPrincipal tbox
        nJ    = nonPrincipal box
        z     = fresh (tbox', box)
        -- x is z
        tbox@(Box tdir x tx nvs) = swap tbox' (pname tbox') z
        toAdd = nK \\ (x' : nJ)
        nL    = nJ \\ nK
        boxL  = subBox nL box
        dir'  = mirror dir
        tdir' = mirror tdir
        -- asumes zd is in the sides of tbox
        pickout zd vcomp = lookBox zd (unCompAs vcomp z)

fill v@(Kan Fill VU tbox@(Box tdir x tx nvs)) box@(Box dir x' vx' nvs')
  -- the cases should be (in order):
  -- 1) W.l.o.g. K subset x', J
  -- 2) x' = x &  dir = tdir
  -- 3) x' = x &  dir = mirror tdir
  -- 4) x `notElem` J (maybe combine with 1?)
  -- 5) x' `notElem` K
  -- 6) x' `elem` K
  | toAdd /= [] = do
    trace "Kan Fill VU Case 1"
    let add :: Side -> Eval Val
        add zc = fillM (return (lookBox zc tbox)) (mapBoxM (`face` zc) box)
    newSides <- sequenceSnd [ (zc,add zc) | zc <- allDirs toAdd ]
    fill v (newSides `appendSides` box)     -- W.l.o.g. nK subset x:nJ
  | x == x' && dir == tdir = do -- assumes K subset x',J
    trace "Kan Fill VU Case 2"
    let boxp = lookBox (x,dir') box  -- is vx'
    principal <- fill (lookBox (x',tdir') tbox)
                      (Box up z boxp (auxsides (x',tdir')))
    nonprincipal <-
      sequenceSnd [ (zc,do let principzc = lookBox zc box
                           fpzc <- principal `face` zc
                           -- "degenerate" along z!
                           let sides = [((x,tdir'),fpzc),((x,tdir),principzc)]
                           fill (lookBox zc tbox)
                                (Box up z principzc (sides ++ auxsides zc)))
                  | zc <- allDirs nK ]
    return $ VFill z (Box tdir x' principal nonprincipal)

  | x == x' && dir == mirror tdir = do -- assumes K subset x',J
    trace "Kan Fill VU Case 3"
    -- the principal side of box must be a VComp
    let -- should be safe given the neutral test at the beginning
        upperbox = unCompAs (lookBox (x,dir') box) x
    nonprincipal <- sequenceSnd
      [ (zc,do let top    = lookBox zc upperbox
                   bottom = lookBox zc box
               -- same as: bottom `face` (x',tdir)
               princ <- top `face` (x',tdir)
               let sides  = [((z,down),bottom),((z,up),top)]
               fill (lookBox zc tbox) (Box tdir' x princ -- "degenerate" along z!
                                       (sides ++ auxsides zc)))
      | zc <- allDirs nK ]
    nonprincipalfaces <- sequenceSnd [ (zc,u `face` (x,dir))
                                     | (zc,u) <- nonprincipal ]
    principal <- fill (lookBox (x,tdir') tbox)
                      (Box up z (lookBox (x,tdir') upperbox)
                       (nonprincipalfaces ++ auxsides (x,tdir')))
    return $ VFill z (Box tdir x' principal nonprincipal)
  | x `notElem` nJ = do  -- assume x /= x' and K subset x', J
    trace "Kan Fill VU Case 4"
    comU <- v `face` (x,tdir) -- Kan Com VU (tbox (z=up))
    let fcbox = mapBoxM (`face` (x,tdir)) box
    xsides <- sequenceSnd [ ((x,tdir), fillM (return comU) fcbox)
                          , ((x,tdir'),
                             fillM (return (lookBox (x,tdir') tbox)) fcbox) ]

    fill v (xsides `appendSides` box)
  | x' `notElem` nK = do -- assumes x,K subset x',J
    trace "Kan Fill VU Case 5"
    -- TODO: Do we need a fresh name?
    let xaux      = unCompAs (lookBox (x,tdir) box) x
        boxprinc  = unFillAs (lookBox (x',dir') box) z
        princnp   = [((z,up),lookBox (x,tdir') xaux),((z,down),lookBox (x,tdir') box)]
                    ++ auxsides (x,tdir')
    principal <- fill (lookBox (x,tdir') tbox) -- tx
                      (Box dir x' (lookBox (x,tdir') boxprinc) princnp)
    nonprincipal <- sequence
      [ do let yup = lookBox yc xaux
           fyup <- yup `face` (x,tdir)
           fpyc <- principal `face` yc
           let np  = [ ((z,up),yup), ((z,down),lookBox yc box)
                     , ((y,c), fyup) -- deg along z!
                     , ((y,mirror c), fpyc) ] ++ auxsides yc
           fb <- fill (lookBox yc tbox) (Box dir x' (lookBox yc boxprinc) np)
           return (yc, fb)
      | yc@(y,c) <- allDirs nK]
    return $ VFill z (Box tdir x' principal nonprincipal)
  | x' `elem` nK = do -- assumes x,K subset x',J
    trace "Kan Fill VU Case 6"
    -- surprisingly close to the last case of the Kan-Com-VU filling
    let upperbox = unCompAs (lookBox (x,dir') box) x
    npintbox <- modBoxM (\zc downside ->
                     let bottom = lookBox zc box
                         top    = lookBox zc upperbox
                         princ  = downside -- same as bottom `face` (x',tdir) and
                                           -- top `face` (x',tdir)
                         sides  = [((z,down),bottom),((z,up),top)]
                     in fill (lookBox zc tbox) (Box tdir' x princ -- deg along z!
                                                (sides ++ auxsides zc)))
                        (subBox (nK `intersect` nJ) box)

    let npint = fromBox npintbox
    npintfacebox <- mapBoxM (`face` (x,tdir)) npintbox
    let principalbox = ([ ((z,down),lookBox (x,tdir') box)
                        , ((z,up)  ,lookBox (x,tdir') upperbox)]
                        ++ auxsides (x,tdir'))
                       `appendSides` npintfacebox
    principal <- fill tx principalbox
    let nplp = lookBox (x',dir) upperbox
    nplnp <- sequenceSnd $
     [ ((x',dir), nplp `face` (x',dir)) -- deg along z!
     , ((x', dir'),principal `face` (x',dir)) ]
     ++  map (second return) (auxsides (x',dir))
      ++ [ (zc,u `face` (x',dir)) | (zc,u) <- sides npintbox ]
    fb <- fill (lookBox (x',dir) tbox) (Box down z nplp nplnp)

    return $ VFill z (Box tdir x' principal (((x',dir),fb) : npint))
    where z     = fresh (v, box)
          nK    = nonPrincipal tbox
          nJ    = nonPrincipal box
          toAdd = nK \\ (x' : nJ)
          nL    = nJ \\ nK
          boxL  = subBox nL box
          dir'  = mirror dir
          tdir' = mirror tdir
          -- asumes zc is in the sides of tbox
          pickout zc vfill = lookBox zc (unFillAs vfill z)
          -- asumes zc is in the sides of tbox
          auxsides zc = [ (yd,pickout zc (lookBox yd box)) | yd <- allDirs nL ]
fill v b = return $ Kan Fill v b

-- Composition (ie., the face of fill which is created)
com :: Val -> Box Val -> Eval Val
-- TODO: is is ok to use runEval like this?
com u box | fst (runEval (isNeutralFill u box)) = return $ VComN u box
com vid@VId{} box@(Box dir i _ _)         = fill vid box `faceM` (i,dir)
com vsigma@VSigma{} box@(Box dir i _ _)   = fill vsigma box `faceM` (i,dir)
com veq@VEquivEq{} box@(Box dir i _ _)    = fill veq box `faceM` (i,dir)
com u@(Kan Com VU _) box@(Box dir i _ _)  = fill u box `faceM` (i,dir)
com u@(Kan Fill VU _) box@(Box dir i _ _) = fill u box `faceM` (i,dir)
com ter@Ter{} box@(Box dir i _ _)         = fill ter box `faceM` (i,dir)
com v box                                 = return $ Kan Com v box

-- Monadic version of com
comM :: Eval Val -> Eval (Box Val) -> Eval Val
comM t b = do
  v  <- t
  b' <- b
  com v b'

-- Conversion functions

(<&&>) :: Monad m => m Bool -> m Bool -> m Bool
(<&&>) = liftM2 (&&)

(<==>) :: (Monad m, Eq a) => a -> a -> m Bool
a <==> b = return (a == b)

andM :: [Eval Bool] -> Eval Bool
andM = liftM and . sequence

conv :: Int -> Val -> Val -> Eval Bool
conv k VU VU                                  = return True
conv k (Ter (Lam x u) e) (Ter (Lam x' u') e') = do
  let v = mkVar k $ support (e, e')
  convM (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
conv k (Ter (Lam x u) e) u' = do
  let v = mkVar k $ support e
  convM (k+1) (eval (Pair e (x,v)) u) (app u' v)
conv k u' (Ter (Lam x u) e) = do
  let v = mkVar k $ support e
  convM (k+1) (app u' v) (eval (Pair e (x,v)) u)
conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
  liftM ((p == p') &&) $ convEnv k e e'
conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
  ((p == p') &&) <$> convEnv k e e'
conv k (Ter (PN (Undef p)) e) (Ter (PN (Undef p')) e') =
  liftM ((p == p') &&) $ convEnv k e e'
conv k (VPi u v) (VPi u' v') = do
  let w = mkVar k $ support [u,u',v,v']
  conv k u u' <&&> convM (k+1) (app v w) (app v' w)
conv k (VSigma u v) (VSigma u' v') = do
  let w = mkVar k $ support [u,u',v,v']
  conv k u u' <&&> convM (k+1) (app v w) (app v' w)
conv k (VId a u v) (VId a' u' v') = andM [conv k a a', conv k u u', conv k v v']
conv k (Path x u) (Path x' u')    = conv k (swap u x z) (swap u' x' z)
  where z = fresh (u,u')
conv k (Path x u) p'              = convM k (return (swap u x z)) (appName p' z)
  where z = fresh u
conv k p (Path x' u')             = convM k (appName p z) (return (swap u' x' z))
  where z = fresh u'
conv k (VExt x b f g p) (VExt x' b' f' g' p') =
  andM [x <==> x', conv k b b', conv k f f', conv k g g', conv k p p']
conv k (VFst u) (VFst u')                     = conv k u u'
conv k (VSnd u) (VSnd u')                     = conv k u u'
conv k (VInh u) (VInh u')                     = conv k u u'
conv k (VInc u) (VInc u')                     = conv k u u'
conv k (VSquash x u v) (VSquash x' u' v')     =
  andM [x <==> x', conv k u u', conv k v v']
conv k (VCon c us) (VCon c' us') =
  liftM (\bs -> (c == c') && and bs) (zipWithM (conv k) us us')
conv k (Kan Fill v box) (Kan Fill v' box')    =
  conv k v v' <&&> convBox k box box'
conv k (Kan Com v box) (Kan Com v' box')      =
  andM [conv k v v', convBox k (swap box x y) (swap box' x' y)]
  where y      = fresh ((v,v'),(box,box'))
        (x,x') = (pname box, pname box')
conv k (VComN v box) (VComN v' box')      =
  andM [conv k v v', convBox k (swap box x y) (swap box' x' y)]
  where y      = fresh ((v,v'),(box,box'))
        (x,x') = (pname box, pname box')
conv k (VFillN v box) (VFillN v' box')      =
  andM [conv k v v', convBox k (swap box x y) (swap box' x' y)]
  where y      = fresh ((v,v'),(box,box'))
        (x,x') = (pname box, pname box')
conv k (VEquivEq x a b f s t) (VEquivEq x' a' b' f' s' t') =
  andM [x <==> x', conv k a a', conv k b b',
       conv k f f', conv k s s', conv k t t']
conv k (VEquivSquare x y a s t) (VEquivSquare x' y' a' s' t') =
  andM [x <==> x', y <==> y', conv k a a', conv k s s', conv k t t']
conv k (VPair x u v) (VPair x' u' v')     =
  andM [x <==> x', conv k u u', conv k v v']
conv k (VSquare x y u) (VSquare x' y' u') =
  andM [x <==> x', y <==> y', conv k u u']
conv k (VComp box) (VComp box')           =
  convBox k (swap box x y) (swap box' x' y)
  where y      = fresh (box,box')
        (x,x') = (pname box, pname box')
conv k (VFill x box) (VFill x' box')      =
  convBox k (swap box x y) (swap box' x' y)
  where y      = fresh (box,box')
conv k (VSPair u v)   (VSPair u' v')   = conv k u u' <&&> conv k v v'
conv k (VSPair u v)   w                =
  conv k u (fstSVal w) <&&> conv k v (sndSVal w)
conv k w              (VSPair u v)     =
  conv k (fstSVal w) u <&&> conv k (sndSVal w) v
conv k (VApp u v)     (VApp u' v')     = conv k u u' <&&> conv k v v'
conv k (VAppName u x) (VAppName u' x') = conv k u u' <&&> (x <==> x')
conv k (VSplit u v)   (VSplit u' v')   = conv k u u' <&&> conv k v v'
conv k (VVar x d)     (VVar x' d')     = return $ (x == x')   && (d == d')
conv k (VInhRec b p phi v) (VInhRec b' p' phi' v') =
  andM [conv k b b', conv k p p', conv k phi phi', conv k v v']
conv k VCircle        VCircle          = return True
conv k VBase          VBase            = return True
conv k (VLoop x)      (VLoop y)        = x <==> y
conv k (VCircleRec f b l v) (VCircleRec f' b' l' v') =
  andM [conv k f f', conv k b b', conv k l l', conv k v v']
conv k VI             VI               = return True
conv k VI0            VI0              = return True
conv k VI1            VI1              = return True
conv k (VLine x)      (VLine y)        = x <==> y
conv k (VIntRec f s e l u) (VIntRec f' s' e' l' u') =
  andM [conv k f f', conv k s s', conv k e e', conv k l l', conv k u u']
conv k _              _                = return False

-- Monadic version of conv
convM :: Int -> Eval Val -> Eval Val -> Eval Bool
convM k v1 v2 = do
  v1' <- v1
  v2' <- v2
  conv k v1' v2'

convBox :: Int -> Box Val -> Box Val -> Eval Bool
convBox k box@(Box d pn _ ss) box'@(Box d' pn' _ ss') =
  if   and [d == d', pn == pn', sort np == sort np']
  then do bs <- sequence [ conv k (lookBox s box) (lookBox s box')
                         | s <- defBox box ]
          return $ and bs
  else return False
  where (np, np') = (nonPrincipal box, nonPrincipal box')

convEnv :: Int -> Env -> Env -> Eval Bool
convEnv k e e' = liftM and $ zipWithM (conv k) (valOfEnv e) (valOfEnv e')

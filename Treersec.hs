{-# LANGUAGE KindSignatures, RankNTypes, GADTs, OverloadedStrings #-}

module Treersec where

import Data.Maybe
import Control.Applicative
import Control.Monad
import Control.Arrow (first, (***))
import Data.List

import SneathLane.Graphics
import SneathLane.Widget hiding (Branch, Leaf)
import SneathLane.BasicWidgets

import Haste

data PP a = PP Int [(Int, Widget GraphicTree a)]

pp_fromWidget (Finish z) = error "fromWidget: Continue widget required"

pp_fromWidget wi@(Continue out _ _ _) = let (Rect x y w h) = graphicTreeBounds out in PP (ceiling $ x + w) (repeat (ceiling (y + h), wi))

pp_above (PP w lgs) (PP w' rgs) =
  let w'' = max w w'
      lgs' = drop (w'' - w) lgs
      rgs' = drop (w'' - w') rgs
  in PP w'' (zipWith (\(lh,lg) (rh,rg) -> (lh + rh, above lg rg)) lgs' rgs')


pp_beside (PP w lgs) (PP w' rgs) = PP (w + w') (go lgs rgs)
  where
    go lgs@((lh,lg):lgs') rgs@((rh,rg):rgs') =
      (max lh rh, beside lg rg) : if lh <= rh then go lgs rgs' else go lgs' rgs

pp_alts (PP w lgs) (PP w' rgs) = PP (min w w') (go w lgs w' rgs)
  where
    go w lgs w' rgs | w < w' = head lgs : go (w + 1) (tail lgs) w' rgs
                    | w' < w = head rgs : go w lgs (w' + 1) (tail rgs)
                    | otherwise = zipWith (\ll rr -> if fst ll <= fst rr then ll else rr) lgs rgs

pp_out w (PP w' gs) = snd $ head $ drop (max 0 (w - w')) gs

straightList pps = pp_alts (foldl1 pp_above pps) (foldl1 pp_beside pps)


instance Functor PP where
  fmap fn (PP w gs) = PP w (map (\(h,g) -> (h,fmap fn g)) gs)

type Printer a = [PP a] -> [PP a]

data Grammar a = Alts [([Grammar a], Printer a)]
               | Term (String -> [String])
               | At Int

llength :: [a] -> Int
llength = length

gfix :: ((Int -> Grammar a) -> Int -> Grammar a) -> (Int -> Grammar a)
gfix gg i = gg (const $ At i) i

term :: (String -> [String]) -> Int -> Grammar a
term s _i = Term s

alts :: [([Int -> Grammar a], Printer a)] -> Int -> Grammar a
alts gs i = Alts ((map.first.map) ($ (i+1)) gs)

data Node = Placeholder
          | Branch Int [Node]
          | Leaf String deriving (Show)

data LinearNode = LPlaceholder
                | LBranch Int
                | LLeaf String deriving (Show)

data GrammarZ a = GrammarZ (Grammar a) [(Grammar a, (Int, Int))] [(Int, Int)]

gzChildren :: GrammarZ a -> [[GrammarZ a]]
gzChildren (GrammarZ (Alts alts) up coords) =
  zipWith (\n gs ->
             let up' m = up ++ [(Alts alts, (n, m))]
             in zipWith (\g m -> case g of
                    At k -> GrammarZ (fst $ (up' m) !! k) (take k (up' m)) (coords ++ [(n,m)])
                    _ -> GrammarZ g (up' m) (coords ++ [(n,m)])) gs [0..]) [0..] (map fst alts)

gzChildren _ = error "gzChildren called on non-Alt gz"

instance Eq (GrammarZ a) where
  (==) (GrammarZ g gs _) (GrammarZ g' gs' _) =
    map snd gs == map snd gs'

gzInject g = GrammarZ g [] []

gzCoords (GrammarZ g gs coords) = coords

lastCoords (Branch _ ns) ((i,j):is) = (i,j) : lastCoords (ns !! j) is
lastCoords node [] = go node
  where
    go (Branch i ns) | not (null ns) = (i, llength ns - 1) : go (last ns)
    go _ = []

commonCoords c1 c2 = case (c1, c2) of
  (x:xs, y:ys) | x == y -> x: commonCoords xs ys
  _ -> []

getSelection g node c1 c2 =
  let top = commonCoords c1 c2
  in case subCoords g g node top c1 c2 of
  Nothing -> [top]
  Just bottom -> [top, bottom]

subCoords gtop g node top c1 c2 = case (top, node) of
  ((i,j):is, Branch _ ns) ->
    let g' = (gzChildren g !! i) !! j
    in (subCoords g' g' (ns !! j) is (tail c1) (tail c2))
  ([], Branch i []) -> Nothing
  ([], Branch i ns) ->
    let ln = llength ns - 1
        (skip,c1',c2') = case (c1, c2) of
          ((_,j):c1',(_,j'):c2') -> (max j j' == ln, c1', c2')
          ([], (_,j'):c2') -> (j' == ln, [], c2')
          ((_,j):c1',[]) -> (j == ln, c1', [])
          ([],[]) -> (False, [], [])
    in if skip || ((gzChildren g !! i) !! ln) /= gtop
       then fmap ((i,ln) :) (subCoords gtop ((gzChildren g !! i) !! ln) (last ns) [] c1' c2')
       else Just [(i,ln)]

  _ -> Nothing


type PreOrder a = [(LinearNode, GrammarZ a)]

getNode :: Node -> [(Int, Int)] -> Node
getNode n [] = n
getNode (Branch _ ns) ((i,j):is) = getNode (ns !! j) is
getNode n _ = n

replaceNode :: GrammarZ a -> Node -> Maybe Node -> [(Int, Int)] -> Node
replaceNode g n splice [] = fromMaybe (parsePreOrder [emptyOrPlaceholder g]) splice

replaceNode g (Branch _ ns) splice ((i,j):is) =
  let n' = replaceNode ((gzChildren g !! i) !! j) (ns !! j) splice is
  in Branch i (take j ns ++ [n'] ++ drop (j+1) ns)

flattenNode :: GrammarZ a -> Node -> PreOrder a
flattenNode g node = case node of
  Placeholder -> [(LPlaceholder, g)]
  Leaf s -> [(LLeaf s, g)]
  Branch i nodes -> (LBranch i, g) : concat (zipWith flattenNode (gzChildren g !! i) nodes)

splitNodeAfter g node cursor = let (xs,y:ys) = splitNodeAt g node cursor in (y:xs, ys)

splitNodeAt g node cursor = (reverse *** id) (go g node cursor)
  where
    go g node cursor =
      case (cursor, node) of
      ([],_) -> ([], flattenNode g node)

      ((i,j):is, Branch _ ns) ->
        let gs = zip (gzChildren g !! i) ns
            pre = take j gs
            ((g',n'):post) = drop j gs
            (pre',post') = go g' n' is
        in ([(LBranch i, g)] ++ (concatMap (uncurry flattenNode) pre) ++ pre',
            post' ++ concatMap (uncurry flattenNode) post)

      _ -> error "Incorrect cursor in splitNodeAt"

parsePreOrder :: PreOrder a -> Node
parsePreOrder xs = let (res,leftover) = go xs in if null leftover then res else error "parsePreorder"
  where
    go (x:xs) = case x of
      (LPlaceholder,_) -> (Placeholder, xs)
      (LLeaf s,_) -> (Leaf s, xs)
      (LBranch i, GrammarZ (Alts alts) _ _) ->
        let (children,xs') = foldl (\(nodes,xs) _g -> let (node,xs') = go xs
                                                      in (node:nodes, xs')) ([], xs) (fst $ alts !! i)
        in (Branch i (reverse children), xs')

preOrderZipUp (xs,ys) = parsePreOrder (reverse xs ++ ys)

cursorBack' g node cursor = preOrderCursor $ preOrderBack $ splitNodeAt g node cursor
cursorBack g node cursor = preOrderCursor $ preOrderBack $ splitNodeAfter g node cursor

preOrderBack :: (PreOrder a, PreOrder a) -> (PreOrder a, PreOrder a)
preOrderBack ([],ys) = ([], ys)
preOrderBack (x:xs, ys) =  case x of
  (LPlaceholder,_) -> (x:xs, ys)
  (LLeaf _,_) -> (x:xs, ys)
  _ -> preOrderBack (xs, x:ys)

preOrderCursor ([],_) = []
preOrderCursor ((_,g):xs, _) = gzCoords g

nextTokens :: (PreOrder a, PreOrder a) -> [(PreOrder a, PreOrder a)]
nextTokens (prev, []) = []
nextTokens (prev, x:next) = logging (map fst prev, map fst (x:next)) $ case x of
  (LLeaf _, _) -> []
  (LPlaceholder, GrammarZ (Term _) _ _) -> [(prev, x:next)]
  (LPlaceholder, g) -> concat $ zipWith (\alt j -> nextTokens ((LBranch j, g):prev, map emptyOrPlaceholder alt ++ next)) (gzChildren g) [0..]
  (LBranch i, g@(GrammarZ (Alts alts) _ _)) ->
    if null $ fst $ alts !! i
    then concat $ zipWith (\alt j -> nextTokens ((LBranch j, g):prev, map emptyOrPlaceholder alt ++ next)) (gzChildren g) [0..]
    else nextTokens (x:prev, next) ++ concatMap (\(a:alt) -> nextTokens (a:prev, alt ++ (x:next))) (recursiveOptions g)


recursiveOptions :: GrammarZ a -> [[(LinearNode, GrammarZ a)]]
recursiveOptions g = go [] g g
  where
    go seen g h =
      if elem h seen
      then []
      else case h of
      GrammarZ (Term _) _ _ -> []
      _ -> concatMap (\(gs,i) ->
                        if null gs
                        then []
                        else map ((LBranch i, h) :) (if last gs == g
                                                     then [map (emptyOrPlaceholder) (init gs)]
                                                     else map (map (emptyOrPlaceholder) (init gs) ++) (go (h:seen) g (last gs)))
                        ) (zip (gzChildren h) [0..])

emptyOrPlaceholder :: GrammarZ a -> (LinearNode, GrammarZ a)
emptyOrPlaceholder g = case g of
  GrammarZ (Alts alts) up _ -> case findIndex null (map fst alts) of
    Just i -> (LBranch i, g)
    Nothing -> (LPlaceholder, g)
  _ -> (LPlaceholder, g)


pp_besides :: [PP a] -> [PP a]
pp_besides = (:[]) . foldr pp_beside (pp_fromWidget $ graphicWidget Nothing (graphicList [noGraphic]))

pp_straightList = (:[]) . straightList

data PPList a = PPList [PP a]

instance Functor PPList where
  fmap f (PPList pps) = PPList $ map (fmap f) pps

concatPPList (PPList xs) (PPList ys) = PPList (xs ++ ys)

renderNode inSel sels w_leaf w_ph mauto g node = (\(PPList [pp]) -> pp_out 500 pp) auto_node
  where
    auto_node = case mauto of
      Just ([],PPList pp) -> let PPList pp' = go [] inSel sels Nothing g node in PPList $ pp_besides (pp ++ pp')
      _ -> go [] inSel sels mauto g node

    go coords inSel sels mauto g node =
      let appendAuto (PPList pp) = case mauto of
            Just ([], PPList pp') -> PPList (pp_besides (pp ++ pp'))
            _ -> PPList pp
          (inSel',sels') = case sels of
            []:xs -> (not inSel, xs)
            _ -> (inSel, sels)
      in case (g, node) of
      (_, Placeholder) -> appendAuto (w_ph (reverse coords) inSel')
      (_, Leaf s) -> appendAuto (w_leaf (reverse coords) s inSel')
      (GrammarZ (Alts alts) _ _, Branch i ch) ->
        let gs' = gzChildren g !! i
            pr = snd $ alts !! i
            ws' = zipWith3 (\j' g' node' ->
                              let sels'' = case sels' of
                                    ((_,j):is):xs | j == j' -> is:xs
                                    _ -> []
                                  mauto' = case mauto of
                                    Just ((_,j):is, auto) | j == j' -> Just (is,auto)
                                    _ -> Nothing
                              in go ((i,j'):coords) inSel' sels'' mauto' g' node') [0..] gs' ch
            (PPList pps) = (if null ws'
                            then PPList []
                            else balancedFold concatPPList ws')
        in PPList (pr pps)

edit :: (forall a. GrammarZ a) -> Node -> Widget GraphicTree z
edit g node = waiting node
  where
    mouseDown node selStart selEnd = do
      let sel = getSelection g node selStart selEnd
      (coords', mouseUp) <- renderNode False sel
                            (\coords s isSel -> hoverable s coords isSel)
                            (\coords isSel -> hoverable "#" coords isSel)
                            Nothing g node
      if mouseUp
        then selected node selStart coords'
        else mouseDown node selStart coords'

    selected node selStart selEnd = do
      let sel = getSelection g node selStart selEnd
      let reselect = renderNode False sel
                 (\coords s inSel -> clickable s coords inSel)
                 (\coords inSel -> clickable "#" coords inSel)
                 Nothing g node
      result <- (fmap Left keyable) `beside` (fmap Right reselect)
      case result of
            Left "x" ->
              let splice = case sel of
                    [top,end] -> Just (getNode node (top ++ end))
                    [top] -> Nothing
              in waiting (replaceNode g node splice (head sel))
            Left "i" -> editing node (cursorBack' g node (head sel))
            Left "a" ->
              let endSel = case sel of
                    [top,end] -> top ++ end
                    [top] -> lastCoords node top
              in editing node (cursorBack g node endSel)
            Right coords' -> mouseDown node coords' coords'


    waiting node = do
      coords <- renderNode False [] (\coords s inSel -> clickable s coords inSel) (\coords inSel -> clickable "#" coords inSel) Nothing g node
      mouseDown node coords coords

    clickable :: String -> z -> Bool -> PPList z
    clickable str ret sel =
      let self = Continue ((\mev -> case mev of
                              EvMouseDown _ _ -> (Nothing, Finish ret)
                              _ -> (Nothing, self)) <$ showText str sel) Nothing Nothing NotFocusable
      in PPList [pp_fromWidget self]

    hoverable :: String -> z -> Bool -> PPList (z, Bool)
    hoverable str ret sel =
      let self = Continue ((\mev -> case mev of
                              EvMouseUp _ _ -> (Nothing, Finish (ret, True))
                              EvMouseMove _ -> (Nothing, Finish (ret, False))
                              _ -> (Nothing, self)) <$ showText str sel) Nothing Nothing NotFocusable
      in PPList [pp_fromWidget self]

    keyable :: Widget GraphicTree String
    keyable = simpleFocus
              (Continue (const (Nothing, keyable) <$ graphicList [noGraphic]) Nothing Nothing)
              (\key -> case key of
                 EvKeyInput "x" -> Finish "x"
                 EvKeyInput "i" -> Finish "i"
                 EvKeyInput "a" -> Finish "a"
                 _ -> keyable)

    showText :: String -> Bool -> GraphicTree ()
    showText str sel =
      let textWidth = measureText codeTS (toJSString str)
          ps = PathStyle Nothing (Just (if sel then RGBA 0 0 0 1 else RGBA 1 1 1 1))
          ts = if sel then codeTS {ts_color = RGBA 1 1 1 1} else codeTS
          components = [
            rectPath ps (textWidth + 4) (fromIntegral (ts_lineHeight codeTS) + 4) 0,
            Text ts (2,2) (toJSString str)
            ]
      in graphicList components

    editing node cursor = do
      res <- renderNode False []
           (\coords s inSel -> clickable s (Left coords) inSel)
           (\coords inSel -> clickable "#" (Left coords) inSel)
           (Just (cursor, PPList [pp_fromWidget $ fmap Right (autoC node cursor)])) g node

      case res of
        Left coords -> mouseDown node coords coords
        Right (Just (node', cursor')) -> editing node' cursor'
        Right Nothing -> waiting node


    autoC node coords =
      let nts = nextTokens (splitNodeAfter g node coords)
      in if null nts
         then Finish Nothing
         else autoComplete codeTS (\str -> concatMap (\(back,(_,g@(GrammarZ (Term f) _ _)):next) ->
                                                        let result s = logging ("result", map fst $ reverse back ++ [(LLeaf s, g)] ++ next) (parsePreOrder $ reverse back ++ [(LLeaf s, g)] ++ next, gzCoords g)
                                                        in map (\s -> (toJSString s, Just $ result s)) (f $ fromJust $ fromJSString str)) nts) "" True

codeTS = TextStyle (RGBA 0 0 0 1.0) 40 46 False False "\"Sans-Serif\""

str a = term (\s -> if s `isPrefixOf` a then [a] else [])

tok_str = term (\s -> if "\"" `isPrefixOf` s
                      then if "\"" `isSuffixOf` s then [s] else [s ++ "\""]
                      else [])

tok_num = term (\s -> if not (null s) && all (`elem` ("0123456789" :: String)) s then [s] else [])

aList :: Grammar a
aList = gfix (\top -> alts [
                ([], pp_besides),
                ([term (const ["a"]), top], pp_besides)
                ]) 0

json :: Grammar a
json = gfix (\any -> alts [
                 ([obj any], id),
                 ([arr any], id),
                 ([simple], id)
                 ]) 0
  where
    obj any = alts [([str "{", sepListNE (kvPair any) (str ","), str "}"], pp_straightList . list_pp)]

    kvPair any = alts [([tok_str, str ":", any], pp_besides)]

    arr any = alts [([str "[", sepListNE any (str ","), str "]"], pp_straightList . list_pp)]


    simple = alts [([tok_str], id),
                   ([tok_num], id)]

    list_pp pps = head pps : (commas $ init $ tail pps) ++ [last pps]

    commas [] = []
    commas [x] = [x]
    commas (x:y:xs) = pp_beside x y : commas xs




sepListNE x y = gfix (\top -> alts [
                          ([x, alts [
                                ([], id),
                                ([y, top], id)
                                ]
                           ], id)
                          ])



widgetMain = runOnCanvas $ \w -> edit (gzInject json) jsonNode
  where
    jsonNode = Branch 1 [Branch 0 [Leaf "[", Placeholder, Leaf "]"]] --(parsePreOrder [emptyOrPlaceholder (gzInject json)])

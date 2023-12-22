-----------------------------------------------------------------------------
-- The LSP handler that provides hover tooltips
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}

module LanguageServer.Handler.InlayHints (inlayHintsHandler) where

import Control.Monad.IO.Class (liftIO)
import Control.Lens ((^.))
import Data.Maybe (mapMaybe)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Language.LSP.Protocol.Types as J
import qualified Language.LSP.Protocol.Message as J
import qualified Language.LSP.Protocol.Lens as J
import Common.Name (Name)
import Common.Range (Range (..), rangeEnd, Pos(..), rangeNull, posNull)
import Type.Pretty (ppType, Env (..), defaultEnv, ppScheme)
import Kind.ImportMap (ImportMap)
import Compiler.Compile (Module(..), Loaded (..))
import Compiler.Options (prettyEnvFromFlags, Flags)
import Syntax.RangeMap (NameInfo (..), RangeInfo (..), rangeMapFindIn)
import Language.LSP.Server (Handlers, sendNotification, requestHandler)
import LanguageServer.Monad (LSM, getLoaded, getLoadedModule, getFlags)
import LanguageServer.Conversions (fromLspPos, toLspRange, toLspPos, fromLspRange)
import LanguageServer.Handler.Hover (formatRangeInfoHover)
-- import Debug.Trace (trace)

-- The LSP handler that provides inlay hints (inline type annotations etc)
inlayHintsHandler :: Handlers LSM
inlayHintsHandler = requestHandler J.SMethod_TextDocumentInlayHint $ \req responder -> do
  let J.InlayHintParams prog doc rng = req ^. J.params
      uri = doc ^. J.uri
      normUri = J.toNormalizedUri uri
  newRng <- liftIO $ fromLspRange normUri rng
  loadedMod <- getLoadedModule normUri
  loaded <- getLoaded normUri
  flags <- getFlags
  let rsp = do -- maybe monad
        l <- loaded
        lm <- loadedMod
        rmap <- modRangeMap lm
        -- trace (show $ rangeMapFindIn newRng rmap) $ return ()
        let env = (prettyEnvFromFlags flags){ context = modName lm, importsMap = loadedImportMap l, showFlavours=False }
        let hints = mapMaybe (toInlayHint env (modName lm)) $ rangeMapFindIn newRng rmap
        let hintsDistinct = Map.fromList $ map (\hint -> (hint ^. J.position, hint)) hints
        return $ Map.elems hintsDistinct
  case rsp of
    Nothing -> responder $ Right $ J.InR J.Null
    Just rsp -> responder $ Right $ J.InL rsp

-- Takes a range and range info and returns an inlay hint if it should be shown
toInlayHint :: Env -> Name -> (Range, RangeInfo) -> Maybe J.InlayHint
toInlayHint env modName (rng, rngInfo) = do
  let rngEnd = rangeEnd rng
      -- should show identifier hint if it's not annotated already
      shouldShow =
        (rngEnd /= posNull) &&
        case rngInfo of
          Id _ info _ -> case info of
            NIValue _ _ isAnnotated -> not isAnnotated
            _ -> False
          _ -> False
  if shouldShow then
    let position = toLspPos rngEnd{posColumn = posColumn rngEnd + 1} in
    let info = T.pack <$> formatInfo env modName rngInfo in
    case info of
      Just typeString -> 
        -- If there is a type to show, show it along with a text edit to accept the type suggestion
        Just $ J.InlayHint position (J.InL typeString) (Just J.InlayHintKind_Type) (Just [J.TextEdit (J.Range position position) typeString]) Nothing (Just True) (Just True) Nothing
      Nothing -> Nothing
  else Nothing

-- Pretty-prints type information for an inlay hint
formatInfo :: Env -> Name -> RangeInfo -> Maybe String
formatInfo env modName rinfo = case rinfo of
  Id qname info isdef ->
    case info of
      NIValue tp _ _ -> Just $ " : " ++ show (ppScheme env tp)
      _ -> Nothing
  _ -> Nothing
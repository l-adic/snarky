module Test.Data.UnionFind where

import Prelude

import Control.Monad.State (State, evalState, execState)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse, traverse_)
import Data.UnionFind (UnionFindData, connected, emptyUnionFind, equivalenceClasses, find, union)
import Effect (Effect)
import Test.QuickCheck ((===))
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Test.Spec.QuickCheck (quickCheck)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

-- | Test state type
type TestState = UnionFindData Int

-- | Helper to run union-find operations
runUF :: forall a. State TestState a -> a
runUF = flip evalState emptyUnionFind

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "Data.UnionFind" do
    describe "Basic operations" do
      it "find returns element for singleton sets" do
        let
          result = runUF do
            root <- find 42
            pure root
        result `shouldEqual` 42

      it "connected returns true for same element" do
        let
          result = runUF do
            connected 42 42
        result `shouldEqual` true

      it "connected returns false for different elements initially" do
        let
          result = runUF do
            connected 1 2
        result `shouldEqual` false

      it "union makes elements connected" do
        let
          result = runUF do
            union 1 2
            connected 1 2
        result `shouldEqual` true

      it "union is transitive" do
        let
          result = runUF do
            union 1 2
            union 2 3
            connected 1 3
        result `shouldEqual` true

      it "path compression works" do
        let
          result = runUF do
            -- Create a chain: 0->1->2->3->4
            union 0 1
            union 1 2
            union 2 3
            union 3 4

            -- Find root of 0 (should compress path)
            root0 <- find 0
            root4 <- find 4

            pure (root0 == root4)

        result `shouldEqual` true

    describe "Property-based tests" do
      it "reflexivity: every element is connected to itself" do
        quickCheck \(x :: Int) ->
          runUF (connected x x) === true

      it "find is idempotent" do
        quickCheck \(x :: Int) ->
          let
            result = runUF do
              root1 <- find x
              root2 <- find root1
              pure (root1 == root2)
          in
            result === true

      it "symmetry: connected(x,y) = connected(y,x)" do
        quickCheck \(x :: Int) (y :: Int) ->
          let
            xy = runUF (connected x y)
            yx = runUF (connected y x)
          in
            xy === yx

      it "transitivity after unions" do
        quickCheck \(x :: Int) (y :: Int) (z :: Int) ->
          let
            result = runUF do
              union x y
              union y z
              connected x z
          in
            result === true

      it "union doesn't break existing connections" do
        quickCheck \(a :: Int) (b :: Int) (c :: Int) (d :: Int) ->
          let
            result = runUF do
              union a b
              wasConnected <- connected a b
              union c d -- This shouldn't affect a-b connection
              stillConnected <- connected a b
              pure (wasConnected && stillConnected)
          in
            result === true

    describe "Equivalence class properties" do
      it "equivalence classes partition the elements" do
        let elements = [ 1, 2, 3, 4, 5 ]
        let
          result = runUF do
            -- Create some unions: {1,2,3}, {4,5}
            union 1 2
            union 2 3
            union 4 5

            -- Check partitioning
            group1 <- traverse (\x -> connected 1 x) elements
            group2 <- traverse (\x -> connected 4 x) elements

            pure { group1, group2 }

        result.group1 `shouldEqual` [ true, true, true, false, false ]
        result.group2 `shouldEqual` [ false, false, false, true, true ]

      it "all elements in same component have same representative" do
        let
          result = runUF do
            union 1 2
            union 2 3
            union 3 4

            root1 <- find 1
            root2 <- find 2
            root3 <- find 3
            root4 <- find 4

            pure [ root1, root2, root3, root4 ]

        let
          allSame = case Array.head result of
            Nothing -> true -- Empty array case
            Just first -> Array.all (_ == first) result
        allSame `shouldEqual` true

      it "different components have different representatives" do
        let
          result = runUF do
            union 1 2
            union 3 4

            root12 <- find 1
            root34 <- find 3

            pure { root12, root34 }

        result.root12 `shouldNotEqual` result.root34

    describe "Performance and edge cases" do
      it "handles many unions efficiently" do
        let
          result = runUF do
            -- Chain all numbers 0..99 together
            Array.range 0 98 # traverse_ \i ->
              union i (i + 1)

            -- Check that 0 and 99 are connected
            connected 0 99

        result `shouldEqual` true

      it "handles repeated unions of same elements" do
        let
          result = runUF do
            union 1 2
            union 1 2 -- Redundant
            union 2 1 -- Redundant but symmetric
            union 1 2 -- Redundant again

            connected 1 2

        result `shouldEqual` true

      it "works with negative numbers" do
        let
          result = runUF do
            union (-1) (-2)
            union (-2) (-3)

            connected (-1) (-3)

        result `shouldEqual` true

      it "works with zero" do
        let
          result = runUF do
            union 0 1
            union 0 (-1)

            allConnected <- do
              c1 <- connected 0 1
              c2 <- connected 0 (-1)
              c3 <- connected 1 (-1)
              pure (c1 && c2 && c3)

            pure allConnected

        result `shouldEqual` true

      it "find creates singleton sets for new elements" do
        let
          result = runUF do
            root1 <- find 42
            root2 <- find 43

            -- Should be their own representatives
            self1 <- pure (root1 == 42)
            self2 <- pure (root2 == 43)

            -- Should not be connected
            notConnected <- connected 42 43 >>= pure <<< not

            pure (self1 && self2 && notConnected)

        result `shouldEqual` true

    describe "Complex scenarios" do
      it "handles star topology" do
        let
          result = runUF do
            -- Create star: center=0, leaves=1,2,3,4,5
            traverse_ (union 0) [ 1, 2, 3, 4, 5 ]

            -- All should be connected to center
            allToCenter <- traverse (connected 0) [ 1, 2, 3, 4, 5 ]

            -- All leaves should be connected to each other
            allPairs <- traverse (\i -> traverse (connected i) [ 1, 2, 3, 4, 5 ]) [ 1, 2, 3, 4, 5 ]

            pure { allToCenter, allPairs }

        result.allToCenter `shouldEqual` [ true, true, true, true, true ]
        -- All pairs should be connected (all true)
        let allTrue = Array.all (Array.all identity) result.allPairs
        allTrue `shouldEqual` true

      it "handles multiple disconnected components" do
        let
          result = runUF do
            -- Component 1: {1,2,3}
            union 1 2
            union 2 3

            -- Component 2: {4,5,6}
            union 4 5
            union 5 6

            -- Component 3: {7} (singleton)

            -- Test connections within components
            comp1 <- do
              c12 <- connected 1 2
              c13 <- connected 1 3
              c23 <- connected 2 3
              pure [ c12, c13, c23 ]

            comp2 <- do
              c45 <- connected 4 5
              c46 <- connected 4 6
              c56 <- connected 5 6
              pure [ c45, c46, c56 ]

            -- Test no connections between components
            between <- do
              c14 <- connected 1 4 >>= pure <<< not
              c17 <- connected 1 7 >>= pure <<< not
              c47 <- connected 4 7 >>= pure <<< not
              pure [ c14, c17, c47 ]

            pure { comp1, comp2, between }

        result.comp1 `shouldEqual` [ true, true, true ]
        result.comp2 `shouldEqual` [ true, true, true ]
        result.between `shouldEqual` [ true, true, true ]

    describe "Equivalence classes enumeration" do
      it "returns all equivalence classes" do
        let
          finalState = execState
            ( do
                -- Create components: {1,2,3}, {4,5}, {6}
                union 1 2
                union 2 3
                union 4 5
                _ <- find 6 -- Make sure 6 is in the structure
                pure unit
            )
            emptyUnionFind

          classes = equivalenceClasses finalState

        -- Should have 3 classes total
        Array.length classes `shouldEqual` 3

        -- Check that all elements appear exactly once across all classes
        let allElements = Array.concatMap identity classes
        Array.sort allElements `shouldEqual` [ 1, 2, 3, 4, 5, 6 ]

        -- Check specific groupings (arrays may be in different order)
        let hasClass123 = Array.any (\cls -> Array.sort cls == [ 1, 2, 3 ]) classes
        let hasClass45 = Array.any (\cls -> Array.sort cls == [ 4, 5 ]) classes
        let hasClass6 = Array.any (\cls -> Array.sort cls == [ 6 ]) classes

        hasClass123 `shouldEqual` true
        hasClass45 `shouldEqual` true
        hasClass6 `shouldEqual` true

      it "returns empty array for empty union-find" do
        let classes = equivalenceClasses (emptyUnionFind :: UnionFindData Int)
        classes `shouldEqual` []

      it "returns singleton classes for disconnected elements" do
        let
          finalState = execState
            ( do
                _ <- find 1
                _ <- find 2
                _ <- find 3
                pure unit
            )
            emptyUnionFind

          classes = equivalenceClasses finalState

        Array.length classes `shouldEqual` 3
        let allElements = Array.concatMap identity classes
        Array.sort allElements `shouldEqual` [ 1, 2, 3 ]
        -- Each class should have exactly one element
        let allSingletons = Array.all (\cls -> Array.length cls == 1) classes
        allSingletons `shouldEqual` true
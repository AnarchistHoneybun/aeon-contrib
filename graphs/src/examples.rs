use algebraeon_sets::structure::{EqSignature, Pairs, SetSignature, UnorderedPair, UnorderedPairs};

use crate::structure::{
    GraphSignature, GraphWithEdgesSignature, LooplessGraphSignature, UndirectedGraphSignature,
};

struct CompleteDirectedGraph<Vertices: SetSignature> {
    vertices: Vertices,

    pairs_of_vertices: UnorderedPairs<Vertices>,
}

impl<Vertices: SetSignature + EqSignature> GraphSignature for CompleteDirectedGraph<Vertices> {
    type Vertices = Vertices;

    fn has_directed_edge(
        &self,
        source: &Vertices::Set,
        target: &Vertices::Set,
    ) -> Result<(), String> {
        if let Err(e) = self.vertices.is_element(source) {
            return Err(format!("Source is not an element of Vertices: {}", e));
        }
        if let Err(e) = self.vertices.is_element(target) {
            return Err(format!("Target is not an element of Vertices: {}", e));
        }
        if self.vertices.equal(source, target) {
            return Err("Complete graphs do not contain loops.".to_string());
        }
        Ok(())
    }
}

impl<Vertices: SetSignature + EqSignature> LooplessGraphSignature
    for CompleteDirectedGraph<Vertices>
{
}

impl<Vertices: SetSignature + EqSignature> GraphWithEdgesSignature
    for CompleteDirectedGraph<Vertices>
{
    type Edges = Pairs<Vertices>;

    fn endpoints(
        &self,
        edge: &<Self::Edges as SetSignature>::Set,
    ) -> UnorderedPair<<Self::Vertices as SetSignature>::Set> {
        self.pairs_of_vertices.new_pair(&edge.0, &edge.1).unwrap()
    }
}

/// A complete bipartite graph K_{m,n} where vertices 0..left_size form the left partition
/// and vertices left_size..total_size form the right partition.
pub struct CompleteBipartiteGraph<Vertices: SetSignature> {
    vertices: Vertices,
    left_size: usize,
    pairs_of_vertices: UnorderedPairs<Vertices>,
}

impl<Vertices: SetSignature> CompleteBipartiteGraph<Vertices> {
    /// Create a new complete bipartite graph K_{left_size, right_size}.
    /// Assumes vertices are enumerable as 0, 1, 2, ..., left_size + right_size - 1
    /// where vertices 0..left_size are in the left partition and
    /// vertices left_size..left_size+right_size are in the right partition.
    pub fn new(vertices: Vertices, left_size: usize) -> Self {
        let pairs_of_vertices = UnorderedPairs::new(vertices.clone());
        Self {
            vertices,
            left_size,
            pairs_of_vertices,
        }
    }

    /// Check if a vertex is in the left partition (assumes vertices are represented as usize)
    fn is_left_vertex(&self, vertex: &<Vertices as SetSignature>::Set) -> Option<bool>
    where
        Vertices::Set: TryInto<usize>,
    {
        if let Ok(v) = vertex.clone().try_into() {
            Some(v < self.left_size)
        } else {
            None
        }
    }
}

impl<Vertices: SetSignature + EqSignature> GraphSignature for CompleteBipartiteGraph<Vertices>
where
    Vertices::Set: TryInto<usize> + Clone,
{
    type Vertices = Vertices;

    fn has_directed_edge(
        &self,
        source: &Vertices::Set,
        target: &Vertices::Set,
    ) -> Result<(), String> {
        // Validate both vertices are in the graph
        if let Err(e) = self.vertices.is_element(source) {
            return Err(format!("Source is not an element of Vertices: {}", e));
        }
        if let Err(e) = self.vertices.is_element(target) {
            return Err(format!("Target is not an element of Vertices: {}", e));
        }

        // No self loops in bipartite graphs
        if self.vertices.equal(source, target) {
            return Err("Bipartite graphs do not contain loops.".to_string());
        }

        // Check if vertices are in different partitions
        let source_is_left = self.is_left_vertex(source);
        let target_is_left = self.is_left_vertex(target);

        match (source_is_left, target_is_left) {
            (Some(source_left), Some(target_left)) => {
                if source_left == target_left {
                    Err("In bipartite graphs, edges only exist between different partitions.".to_string())
                } else {
                    Ok(())
                }
            }
            _ => Err("Unable to determine vertex partition.".to_string()),
        }
    }
}

impl<Vertices: SetSignature + EqSignature> LooplessGraphSignature
    for CompleteBipartiteGraph<Vertices>
where
    Vertices::Set: TryInto<usize> + Clone,
{
}

impl<Vertices: SetSignature + EqSignature> UndirectedGraphSignature
    for CompleteBipartiteGraph<Vertices>
where
    Vertices::Set: TryInto<usize> + Clone,
{
}

impl<Vertices: SetSignature + EqSignature> GraphWithEdgesSignature
    for CompleteBipartiteGraph<Vertices>
where
    Vertices::Set: TryInto<usize> + Clone,
{
    type Edges = UnorderedPairs<Vertices>;

    fn endpoints(
        &self,
        edge: &<Self::Edges as SetSignature>::Set,
    ) -> UnorderedPair<<Self::Vertices as SetSignature>::Set> {
        edge.clone()
    }
}

#[cfg(test)]
mod tests {
    use algebraeon_sets::structure::{
        EnumeratedFiniteSetStructure, EqSignature, Pairs, UnorderedPairs,
    };

    use crate::{
        examples::{CompleteDirectedGraph, CompleteBipartiteGraph},
        structure::{GraphSignature, GraphWithEdgesSignature},
    };

    #[test]
    fn test_k5() {
        let fin5 = EnumeratedFiniteSetStructure::new(5);
        let fin5_unordered_pairs = UnorderedPairs::new(fin5.clone());
        let k5 = CompleteDirectedGraph {
            vertices: fin5.clone(),
            pairs_of_vertices: fin5_unordered_pairs.clone(),
        };

        assert!(k5.has_directed_edge(&1, &2).is_ok());
        assert!(k5.has_directed_edge(&1, &1).is_err());
        assert!(k5.has_directed_edge(&5, &1).is_err());

        let fin5_pairs = Pairs::new(fin5.clone());

        let e1 = fin5_pairs.clone().new_pair(1.clone(), 2.clone()).unwrap();
        let e2 = fin5_pairs.clone().new_pair(2.clone(), 1.clone()).unwrap();
        assert!(fin5_unordered_pairs.equal(&k5.endpoints(&e1), &k5.endpoints(&e2)));
    }

    #[test]
    fn test_complete_bipartite_k23() {
        // Create K_{2,3} with vertices 0,1 in left partition and 2,3,4 in right partition
        let fin5 = EnumeratedFiniteSetStructure::new(5);
        let k23 = CompleteBipartiteGraph::new(fin5.clone(), 2);

        // Test valid edges (between different partitions)
        assert!(k23.has_directed_edge(&0, &2).is_ok()); // left to right
        assert!(k23.has_directed_edge(&1, &3).is_ok()); // left to right
        assert!(k23.has_directed_edge(&2, &0).is_ok()); // right to left
        assert!(k23.has_directed_edge(&4, &1).is_ok()); // right to left

        // Test invalid edges (within same partition)
        assert!(k23.has_directed_edge(&0, &1).is_err()); // both in left
        assert!(k23.has_directed_edge(&2, &3).is_err()); // both in right
        assert!(k23.has_directed_edge(&3, &4).is_err()); // both in right

        // Test self loops (not allowed)
        assert!(k23.has_directed_edge(&0, &0).is_err());
        assert!(k23.has_directed_edge(&2, &2).is_err());

        // Test invalid vertices
        assert!(k23.has_directed_edge(&5, &0).is_err());
        assert!(k23.has_directed_edge(&0, &6).is_err());
    }

    #[test]
    fn test_bipartite_edge_symmetry() {
        // Test that bipartite graph is undirected (symmetric)
        let fin4 = EnumeratedFiniteSetStructure::new(4);
        let k22 = CompleteBipartiteGraph::new(fin4, 2);

        // For undirected graphs, (u,v) should have same validity as (v,u)
        assert_eq!(
            k22.has_directed_edge(&0, &2).is_ok(),
            k22.has_directed_edge(&2, &0).is_ok()
        );
        assert_eq!(
            k22.has_directed_edge(&1, &3).is_ok(),
            k22.has_directed_edge(&3, &1).is_ok()
        );
    }

    #[test]
    fn test_bipartite_edges() {
        let fin5 = EnumeratedFiniteSetStructure::new(5);
        let k23 = CompleteBipartiteGraph::new(fin5.clone(), 2);

        // Create an edge between left vertex 0 and right vertex 2
        let edge_02 = k23.pairs_of_vertices.new_pair(&0, &2).unwrap();
        let endpoints = k23.endpoints(&edge_02);
        
        // Verify the endpoints are the same as the original edge
        assert!(k23.pairs_of_vertices.equal(&edge_02, &endpoints));
    }
}
import React, { useEffect, useRef } from 'react';
import { DataSet, Network } from 'vis-network/standalone';

interface Implication {
  lhs: string;
  rhs: string;
}

interface DiagramProps {
  implications: Implication[];
  nonimplications: Implication[];
}

const Diagram: React.FC<DiagramProps> = ({ implications, nonimplications }) => {
  const containerRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (containerRef.current) {
      // Create nodes and edges
      const nodes = new DataSet<{ id: string, label: string}>([]);
      const edges = new DataSet<{ id:string, from: string, to: string, arrows?:string, color: string }>([]);

      const addNodeIfNotExists = (id: string, label: string) => {
        if (!nodes.get(id)) {
          nodes.add({ id, label });
        }
      };

      // Add nodes and edges for implications
      implications.forEach(({ lhs, rhs }) => {
        addNodeIfNotExists(lhs, lhs);
        addNodeIfNotExists(rhs, rhs);
        edges.add({ id: `implication-${lhs}-${rhs}`, from: lhs, to: rhs, arrows: 'to', color: '#97c2fc' }); // Implication edge color
      });

      // Add nodes and edges for non-implications
      nonimplications.forEach(({ lhs, rhs }) => {
        addNodeIfNotExists(lhs, lhs);
        addNodeIfNotExists(rhs, rhs);
        edges.add({ id: `nonimplication-${lhs}-${rhs}`, from: lhs, to: rhs, arrows: 'to', color: '#ff9999' }); // Non-implication edge color
      });

      // Create a network
      const data = { nodes, edges };
      const options = {
        layout: {
          hierarchical: {
            direction: 'UD', // Up-Down layout
            sortMethod: 'hubsize'
          },
        },
        physics: {
          enabled: true,
          solver: 'barnesHut',
        },
      };

      const network = new Network(containerRef.current, data, options);

      // Cleanup on unmount
      return () => {
        network.destroy();
      };
    }
  }, [implications, nonimplications]);

  return <div ref={containerRef} style={{ height: '500px', width: '100%' }} />;
};

export default Diagram;

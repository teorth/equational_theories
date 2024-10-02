import React, { useEffect, useRef } from 'react';
import { DataSet, Network } from 'vis-network/standalone';

interface Implication {
  lhs: string;
  rhs: string;
}

interface Facts {
  satisfied: string[];
  refuted: string[];
}

interface DiagramProps {
  implications: Implication[];
  facts: Facts[];
}

const Diagram: React.FC<DiagramProps> = ({ implications, facts }) => {
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

      const addEdgeIfNotExists = (data : {
          id: string;
          from: string;
          to: string;
          arrows?: string;
          color: string;
      }) => {
        if (!edges.get(data.id)) {
          edges.add(data);
        }
      };

      // Add nodes and edges for implications
      implications.forEach(({ lhs, rhs }) => {
        addNodeIfNotExists(lhs, lhs);
        addNodeIfNotExists(rhs, rhs);
        addEdgeIfNotExists({ id: `implication-${lhs}-${rhs}`, from: lhs, to: rhs, arrows: 'to', color: '#97c2fc' }); // Implication edge color
      });

      // Add nodes and edges for non-implications
      facts.forEach(({ satisfied, refuted }) => {
        satisfied.forEach(lhs => {
          addNodeIfNotExists(lhs, lhs);
          refuted.forEach(rhs => {
            addNodeIfNotExists(rhs, rhs);
            addEdgeIfNotExists({ id: `nonimplication-${lhs}-${rhs}`, from: lhs, to: rhs, arrows: 'to', color: '#ff9999' }); // Non-implication edge color
          });
        });
      });

      // Create a network
      const data = { nodes, edges };
      const options = {
        layout: {
          randomSeed: 2, // Seed for random layout (to get consistent results)
          improvedLayout: true, // Allow for some improvement on the random layout
        },
        physics: {
          enabled: true,
          solver: 'repulsion', // Use repulsion solver for more dynamic placement
          repulsion: {
            nodeDistance: 150, // Distance between nodes
            centralGravity: 0.3, // Pull nodes towards the center
            springLength: 100, // Default length of the springs
          },
        },
        nodes: {
          shape: 'dot', // Change to dot shape for simplicity
          size: 12, // Set a uniform size for nodes
          color: {
            border: '#2B7CE9',
            background: '#97c2fc',
          },
          font: {
            size: 18,
            color: '#000000',
          },
        },
        edges: {
          color: {
            inherit: 'from',
          },
          arrows: {
            to: {
              enabled: true,
            },
          },
        },
        interaction: {
          hover: true,
          tooltipDelay: 200,
        },
      };

      const network = new Network(containerRef.current, data, options);

      // Cleanup on unmount
      return () => {
        network.destroy();
      };
    }
  }, [implications, facts]);

  return <div ref={containerRef} style={{ height: '500px', width: '100%' }} />;
};

export default Diagram;

#include <CGAL/Exact_predicates_inexact_constructions_kernel.h>
#include <CGAL/Projection_traits_xy_3.h>
#include <CGAL/Triangulation_vertex_base_with_info_2.h> //added by me
#include <CGAL/Triangulation_face_base_with_info_2.h> //added by me
#include <CGAL/Delaunay_triangulation_2.h>
#include<string.h>
#include<fstream>
#include<vector>
#if defined(__APPLE__)
#include <GLUT/glut.h>
#else
#include <GL/glut.h>
#endif
#define NENDS 2
bool BOUNDARY_SAMPLE;
float new_pts[100000][3];
float edge_length[100000]; // used to handle outlier
int counter_var =0; // used to handle outlier
float Q1,Q2,Q3;

typedef CGAL::Exact_predicates_inexact_constructions_kernel K;
typedef CGAL::Triangulation_vertex_base_with_info_2<int[100],K> Vb;
typedef CGAL::Triangulation_face_base_with_info_2<int[3],K> Fb;
typedef CGAL::Triangulation_data_structure_2<Vb,Fb> Tds;
typedef CGAL::Delaunay_triangulation_2<K,Tds> Delaunay;


// data structres for cycle removal
const int N = 100000;
int color[N];
int par[N];
int num_edges=0;
std::vector<int> graph[N];
std::vector<int> cycles[N];
int no_of_cycles=0;
int choice=0;

// data structres for cycle removal

typedef Delaunay::Point   Point;
std::vector<Point> cycle_vertices(N);
class Edge
{
public:
  Point source;
  Point target;
 };

typedef std::vector<Edge> Edges;
Edges shape,bdry,marked;
GLdouble width, height;
int wd,loop,ends1[NENDS][2],di=0;
Delaunay dt;
float len;
Point input_points[10000];
int vertex_count=0,minx=9999,miny=9999,maxx=0,maxy=0;
float vertex_size;
void init(void)
{
    width  = 1280.0;
    height = 800.0;
    ends1[0][0] = (int)(0.25*width);
    ends1[0][1] = (int)(0.75*height);
    ends1[1][0] = (int)(0.75*width);
    ends1[1][1] = (int)(0.25*height);
    return;
}
void reshape(int w, int h)
{
    width = (GLdouble) w;
    height = (GLdouble) h;
    glViewport(0, 0, (GLsizei) width, (GLsizei) height);
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    glRotatef(-180,180,0,1);
    glOrtho(minx-20.0,maxx+20.0,miny-20.0,maxy+20.0, -1.f, 1.f);
    return;
}
void kbd(unsigned char key, int x, int y)
{
    switch((char)key) {
        case 'q':
        case 27:
            glutDestroyWindow(wd);
            exit(0);
        default:
            break;
    }
    return;
}
void drawFilledCircle(GLfloat x, GLfloat y, GLfloat radius)
{
    glEnable(GL_BLEND);
   // glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    int i,triangleAmount = 100;
    GLfloat twicePi = 2.0f * 3.14159265;
    glBegin(GL_TRIANGLE_FAN);
    glVertex2f(x, y);
    for(i = 0; i <= triangleAmount;i++)
        glVertex2f(x + (radius * cos(i *  twicePi / triangleAmount)),y + (radius * sin(i * twicePi / triangleAmount)));
    glEnd();
}
char *fname;
void pointset(void)
{
    glLineWidth(2.5);
    glEnable( GL_LINE_SMOOTH );
    glEnable( GL_POLYGON_SMOOTH );
    glHint( GL_LINE_SMOOTH_HINT, GL_NICEST );
    glHint( GL_POLYGON_SMOOTH_HINT, GL_NICEST );

    glColor3f(1,0.15,0);
    for(int i=0;i<vertex_count;i++)
       drawFilledCircle(input_points[i].x(),input_points[i].y(),vertex_size);

   if(choice == 2)
    {
        // to write the edge info in to a file
        char data[100];
        std::ofstream outfile1,outfile2;
        outfile2.open("afile1.dat");


        glColor3f(0.7, 0.25, .75);
         std::vector<int> ls; //no_of_cycles
         for(int k=0;k<no_of_cycles;k++)
            {
                ls = cycles[k];
                if(ls.size()>10)
                {
                    int i=0;
                    for(; i < ls.size()-1; i++)
                    {
                        glBegin(GL_LINES);
                        glVertex2f(cycle_vertices[ls[i]].x(),cycle_vertices[ls[i]].y());
                        glVertex2f(cycle_vertices[ls[i+1]].x(),cycle_vertices[ls[i+1]].y());
                        glEnd();
                        outfile2 << cycle_vertices[ls[i]].x()<<" "<<cycle_vertices[ls[i]].y()<<" "<<cycle_vertices[ls[i+1]].x()<<" "<<cycle_vertices[ls[i+1]].y()<<std::endl;
                    }
                    glBegin(GL_LINES);
                    glVertex2f(cycle_vertices[ls[i]].x(),cycle_vertices[ls[i]].y());
                    glVertex2f(cycle_vertices[ls[0]].x(),cycle_vertices[ls[0]].y());
                    glEnd();
                    outfile2 << cycle_vertices[ls[i]].x()<<" "<<cycle_vertices[ls[i]].y()<<" "<<cycle_vertices[ls[0]].x()<<" "<<cycle_vertices[ls[0]].y()<<std::endl;
                 }
             }
          outfile2.close();
    }


}
void display(void)
{
    glClear(GL_COLOR_BUFFER_BIT);
    pointset();
    glFlush();
    return;
}
float distance(Point a, Point b)
{
    return (float)(sqrt((((a.x()-b.x())*(a.x()-b.x())))+abs(((a.y()-b.y())*(a.y()-b.y())))));
}
bool isFinite(Delaunay::All_faces_iterator afi) /*Checking whether the face is finite or not*/
{
  if(afi->vertex(0) != dt.infinite_vertex() && afi->vertex(1) != dt.infinite_vertex() && afi->vertex(2) != dt.infinite_vertex())
      return true;
  return false;
}
void init_edges_status(void)
{

    int indx =0;
    for (Delaunay::Finite_vertices_iterator it = dt.finite_vertices_begin(); it != dt.finite_vertices_end(); it++)
    {
        indx =0;
        Delaunay::Vertex_circulator circulator = dt.incident_vertices(it), done(circulator);
        do
        {
            it->info()[indx] = -1;
            indx++;
        } while(++circulator != done);

        it->info()[99] = indx; //degree of the vertex
 //       it->info()[98] = 2;  //types of vertex ; 1 = outlier,2 = non-outlier, 3 = oulier candiate
   //     it->info()[97] = 0; //no of marked edges(partially/fully)
     //   it->info()[96] = 2; // whether connected to outlier; 1 = connected to outlier, 2 = not connected to outlier
    }

    //init face satus
     for (Delaunay::Finite_faces_iterator fit = dt.finite_faces_begin(); fit != dt.finite_faces_end(); fit++)
     {
         for(int k=0;k<=2;k++)
         {
             fit->info()[k]=0;
         }
     }

}
bool test_status_of_edge(Delaunay::Vertex::Vertex_handle vh1,Delaunay::Vertex::Vertex_handle circ)
{
    int indx =0;
    Delaunay::Vertex_circulator circulator = dt.incident_vertices(circ), done(circulator);

    do
    {

            if(circulator->point() == vh1->point() )
            {
               if(circ->info()[indx]!=1 )
                {
                    return 1;
                }
               else
                   return 0;

            }

        indx++;
   } while(++circulator != done);
}
void reconstruct(void)
{
    int flg =0;


    for (Delaunay::Finite_vertices_iterator it = dt.finite_vertices_begin(); it != dt.finite_vertices_end(); it++)
    {
        float dist[100000];
        int di=0;
        int cntu =1;
        flg=0;
        Delaunay::Vertex_circulator circulator = dt.incident_vertices(it), done(circulator);
        do
        {
            dist[di]=distance(circulator->point(),it->point());

	    edge_length[counter_var] = dist[di]; // used to handle outlier
	    di++;
            counter_var++; // used to handle outlier
        } while(++circulator != done);


        float big=0,small=9999;

        while(cntu)
        {
            cntu =0;
            for(int i=0;i<di;i++)
              {
                 if(dist[i]>big && it->info()[i] != 1)
                 {
                      big=dist[i];
                      flg = i;
                 }

                if(dist[i]<small)
                   small=dist[i];

              }

            if(big > 2*small)
            {
                it->info()[flg] = 1;
                flg=0;
                big=0;
                small=9999;
                cntu=1;
             }

        }

      }

}

 bool test_conv_vertex_candature(Delaunay::Vertex::Vertex_handle vh1)
 {
     int indx =0;
     Delaunay::Vertex_circulator circulator = dt.incident_vertices(vh1), done(circulator);

     do
     {

         if(dt.is_infinite (circulator))

              return 1;
         indx++;
    } while(++circulator != done);

     return 0;
 }

int median(int l, int r)
{
	int n = r - l + 1;
	n = (n + 1) / 2 - 1;
	return n + l;
}

float IQR(float* a, int n)
{
	Q1 =0;
	Q3 =0;
	Q3 =0;
	std::sort(a, a + n);

	// Index of median of entire data
	int mid_index = median( 0, n);
         Q2 = a[mid_index];

	// Median of first half
	 Q1 = a[median(0, mid_index)];

	// Median of second half
	 Q3 = a[median( mid_index + 1, n)];


	return (Q3-Q1);
}
void mark_othersideofedge(Delaunay::Vertex::Vertex_handle vh1,Delaunay::Vertex::Vertex_handle circ)
{
    int indx =0;
    Delaunay::Vertex_circulator circulator = dt.incident_vertices(circ), done(circulator);

    do
    {

            if(circulator->point() == vh1->point() )
            {
               circ->info()[indx]=1;

            }

        indx++;
   } while(++circulator != done);
}
void mark_outlier_edges()
{
    int indx1 =0;
    int degree_of_vertex =0,no_partially_marked_edges =0,no_unmarked_edges = 0,no_fully_marked_edges = 0;
    bool outlier_candidate = 0;
      float iqr =0, edge_len =0,ufence =0;
     int flag =0;
     iqr = IQR(edge_length,counter_var);

     ufence = Q3 + iqr*1.5;



    for (Delaunay::Finite_vertices_iterator it = dt.finite_vertices_begin(); it != dt.finite_vertices_end(); it++)
    {
        indx1 =0;
        degree_of_vertex =0;
        no_partially_marked_edges=0;
        outlier_candidate = 0;
        no_unmarked_edges = 0;
        no_fully_marked_edges= 0;




        Delaunay::Vertex_circulator circulator = dt.incident_vertices(it), done(circulator);
        do
        {
            if(!dt.is_infinite (circulator))
            {
                 degree_of_vertex++;
                 if(it->info()[indx1]!=1 )
                {
                     if(!test_status_of_edge(it,circulator) )
                     {
                         no_partially_marked_edges++;

                     }
                     else
                     {
                         no_unmarked_edges++;
                     //    if(test_outlier_candature(it,circulator))
                        //     no_outlier_neigbors++;
                     }

                }
            }
            else
            {
               outlier_candidate = 1;
   //            it->info()[98] = 3; //outlier candiate; connected to infinite vertex
            }

           indx1++;

        } while(++circulator != done);


        no_fully_marked_edges = degree_of_vertex - (no_partially_marked_edges + no_unmarked_edges);

       if( (degree_of_vertex == no_partially_marked_edges+no_fully_marked_edges) )
        {
            indx1 =0;
    //        std::cout<<"II="<<" degree ="<<degree_of_vertex<<"  Partially marked ="<<no_partially_marked_edges<<"  no_umark ="<<no_unmarked_edges<<" no of outlier negbor "<<no_outlier_neigbors<<"  no_fully_marked_edges "<<no_fully_marked_edges<<std::endl;
            Delaunay::Vertex_circulator circulator1 = dt.incident_vertices(it), done(circulator1);
             do
             {
                 it->info()[indx1]=1;
                 indx1++;
		 mark_othersideofedge(it,circulator1);
               } while(++circulator1 != done);

        }
      else if(no_partially_marked_edges > no_unmarked_edges)
	{
		indx1 =0;flag =0;
		Delaunay::Vertex_circulator circulator = dt.incident_vertices(it), done(circulator);

		 do
		 {

            		if(!dt.is_infinite (circulator))
			 {
				if(it->info()[indx1]!=1 )
				 {
					if(!test_status_of_edge(it,circulator) )
                    			 {
					   edge_len =distance(circulator->point(),it->point());
						//no_partially_marked_edges++;
                                           if(edge_len < ufence)
   						flag++;

					  }
				  }
			  }
                         indx1++;
         	} while(++circulator != done);
		indx1 =0;
		if(flag == 0)
		{
	//		 std::cout<<"III="<<" degree ="<<degree_of_vertex<<"  Partially marked ="<<no_partially_marked_edges<<"  no_umark ="<<no_unmarked_edges<<" no of outlier negbor "<<no_outlier_neigbors<<"  no_fully_marked_edges "<<no_fully_marked_edges<<std::endl;
			Delaunay::Vertex_circulator circulator1 = dt.incident_vertices(it), done(circulator1);

            		 do

             		{

                 		it->info()[indx1]=1;
                 		indx1++;
				mark_othersideofedge(it,circulator1);

               		}while(++circulator1 != done);

		}
	 }

    }

}
int calculate_num_edges_marked(Delaunay::Vertex::Vertex_handle vh)
{
    int indx1 =0;
    int marked_edges =0;

        Delaunay::Vertex_circulator circulator = dt.incident_vertices(vh), done(circulator);
        do
        {
            if(!dt.is_infinite (circulator))
            {
                 if(vh->info()[indx1]==1 || !test_status_of_edge(vh,circulator)  )
                 {
                     marked_edges++;
                 }
            }
            indx1++;

        } while(++circulator != done);

  return marked_edges;

}

void retain_fullymarked_shape_edges()
{
    int indx1 =0;

    for (Delaunay::Finite_vertices_iterator it = dt.finite_vertices_begin(); it != dt.finite_vertices_end(); it++)
    {
        indx1 =0;
        Delaunay::Vertex_circulator circulator = dt.incident_vertices(it), done(circulator);
        do
        {
            if(it->info()[indx1]==1 && calculate_num_edges_marked(it) == 1 )
            {
                if(!dt.is_infinite (circulator))
                  {
                    if(!test_status_of_edge(it,circulator) && calculate_num_edges_marked(circulator) ==1)
                     {
			if(test_conv_vertex_candature(it) && test_conv_vertex_candature(circulator))
			{
				; //do nothing
			}
			else
			{
                     		 it->info()[indx1]=-1; it->info()[97] = it->info()[97] -1 ;
			}
                     }
                  }
            }
            indx1++;

        } while(++circulator != done);

    }

}


void retain_partiallymarked_shape_edges(void)
{

        int indx1 =0;
        for (Delaunay::Finite_vertices_iterator it = dt.finite_vertices_begin(); it != dt.finite_vertices_end(); it++)
        {
            indx1 =0;
            Delaunay::Vertex_circulator circulator = dt.incident_vertices(it), done(circulator);
            do
            {
                if(it->info()[indx1]==1 )
                {
                    if(!dt.is_infinite (circulator))
                      {
                        if(test_status_of_edge(it,circulator) )
                         {
                          it->info()[indx1]=-1;
                         }
                      }
                }
                indx1++;

            } while(++circulator != done);

        }

}
void collect_shape_edges(void)
{
    for (Delaunay::Finite_vertices_iterator it = dt.finite_vertices_begin(); it != dt.finite_vertices_end(); it++)
    {
        int indx =0;
        Delaunay::Vertex_circulator circulator = dt.incident_vertices(it), done(circulator);
        do
        {
            if(it->info()[indx]!=1 )
            {
                 Edge e;
                e.source = circulator->point();
                e.target = it->point();
                shape.push_back(e);
            }
            indx++;

        } while(++circulator != done);

    }
}


void collect_boundary_edges(void)
{

    // marking the off the shape edges
     float dist[10000];
     int indx=0;
     for (Delaunay::Finite_faces_iterator fit = dt.finite_faces_begin(); fit != dt.finite_faces_end(); fit++)
     {

        for(int k=0;k<=2;k++)
        {
            indx =0;
            Delaunay::Vertex_circulator circulator = dt.incident_vertices(fit->vertex(k)), done(circulator);
            do
            {
                if(fit->vertex(k)->info()[indx]==1 )
                {
                    if(circulator->point() == fit->vertex((k+1)%3)->point() )
                    {
                        fit->info()[(k+2)%3] = 1;
                    }
                    if(circulator->point() == fit->vertex((k+2)%3)->point() )
                    {
                        fit->info()[(k+1)%3] = 1;
                    }
                }
                indx++;
           } while(++circulator != done);
        }

      }
   // collecting the boundary edges
   for (Delaunay::Finite_faces_iterator fit = dt.finite_faces_begin(); fit != dt.finite_faces_end(); fit++)
   {
       int edgesum = fit->info()[0] + fit->info()[1] + fit->info()[2];
       if(edgesum == 0)
       {
            if(!isFinite(fit->neighbor(0)))
            {
                Edge e;
                e.source = fit->vertex(1)->point();
                e.target = fit->vertex(2)->point();
                bdry.push_back(e);
            }
            if(!isFinite(fit->neighbor(1)))
            {
                Edge e;
                e.source = fit->vertex(2)->point();
                e.target = fit->vertex(0)->point();
                bdry.push_back(e);
            }
            if(!isFinite(fit->neighbor(2)))
            {
                Edge e;
                e.source = fit->vertex(0)->point();
                e.target = fit->vertex(1)->point();
                bdry.push_back(e);
            }
       }
       else if(edgesum == 1)
       {
           if(fit->info()[0] ==1 )
           {
               Edge e,e1;
               e.source = fit->vertex(0)->point();
               e.target = fit->vertex(1)->point();
               bdry.push_back(e);
             e1.source = fit->vertex(2)->point();
               e1.target = fit->vertex(0)->point();
               bdry.push_back(e1);

           }
           else if(fit->info()[1] ==1 )
           {
               Edge e,e1;
               e.source = fit->vertex(1)->point();
               e.target = fit->vertex(2)->point();
               bdry.push_back(e);
               e1.source = fit->vertex(0)->point();
               e1.target = fit->vertex(1)->point();
               bdry.push_back(e1);

           }
           else if(fit->info()[2] ==1 )
           {
               Edge e,e1;
               e.source = fit->vertex(1)->point();
               e.target = fit->vertex(2)->point();
               bdry.push_back(e);
               e1.source = fit->vertex(2)->point();
               e1.target = fit->vertex(0)->point();
               bdry.push_back(e1);

           }
       }
      else if(edgesum ==2)
       {
           if(fit->info()[0] !=1 )
           {
                 Edge e;
                e.source = fit->vertex(1)->point();
                e.target = fit->vertex(2)->point();
                 bdry.push_back(e);
           }
           else if(fit->info()[1] !=1 )
           {
                 Edge e;
                e.source = fit->vertex(2)->point();
                e.target = fit->vertex(0)->point();
                 bdry.push_back(e);
           }
           else if(fit->info()[2] !=1 )
           {
                 Edge e;
                e.source = fit->vertex(0)->point();
                e.target = fit->vertex(1)->point();
                 bdry.push_back(e);
           }

       }

   }

}
// CYCLE REMOVAL CODE/////////////////////////////////////
int point_already_exist(Point p,int indx)
{
    for(int k=0;k<indx;k++)
    {
        if(cycle_vertices[k]==p)
        {
            return k;
        }
    }
    return -1;
}
// add the edges to the graph
void addEdge(int u, int v)
{
        graph[u].push_back(v);
        graph[v].push_back(u);
}


void dfs_cycle(int u, int p, int color[], int par[])
  {

          // already (completely) visited vertex.
          if (color[u] == 2) {
                  return;
          }

          // seen vertex, but was not completely visited -> cycle detected.
          // backtrack based on parents to find the complete cycle.
        //  std::cout << "color of U "<< color[u]<< std::endl;
          if (color[u] == 1)
          {

                  int cur = p;
                  cycles[no_of_cycles].push_back(cur);

                  while (cur != u)
                  {
                          cur = par[cur];
                          cycles[no_of_cycles].push_back(cur);
                  }
                  no_of_cycles++;
                  return;
           }

          par[u] = p;

          // partially visited.
          color[u] = 1;

          // simple dfs on graph
          for (int v : graph[u]) {

                  // if it has not been visited previously
                  if (v == par[u])
                  {
                          continue;
                  }
                 dfs_cycle(v, u, color, par);
          }

          // completely visited.
          color[u] = 2;

  }

void remove_cycle(void)
{

    int loc1=-1,loc2=-1,indx =0;

    for(int i=0;i<bdry.size();i++)
    {
        loc1 = point_already_exist(bdry[i].source,indx);
        loc2 = point_already_exist(bdry[i].target,indx);

        if(loc1 == -1)
        {
            cycle_vertices[indx] = bdry[i].source;
            indx++;

        }
        if(loc2 == -1)
        {
            cycle_vertices[indx] = bdry[i].target;
            indx++;

        }

        if(loc1 == -1 && loc2 == -1)
        {
             addEdge((indx-2), (indx-1));
             num_edges++;

        }
        else if(loc1 == -1 && loc2 != -1)
        {
            addEdge((indx-1), loc2);
            num_edges++;
        }
        else if(loc1 != -1 && loc2 == -1)
        {
            addEdge(loc1,(indx-1));
            num_edges++;
        }
        else if(loc1 != -1 && loc2 != -1)
        {
                 addEdge(loc1,loc2);
                 num_edges++;
        }
    }

     for (int k=0;k<indx;k++)
     {
         if (color[k]==2)
            continue;

         dfs_cycle(k, 1, color, par);
     }

     int no =1;
  /*   for (int i = 0; i <= no_of_cycles; i++)
      {
          if(cycles[i].size()>10)
            {
               std::cout << "Cycle Number " << no++ << ": ";
               for (int x : cycles[i])
                      std::cout << x << " ";
               std::cout <<std::endl;
            }
       }*/
}

void marked_edges(void)
{
    for (Delaunay::Finite_faces_iterator fit = dt.finite_faces_begin(); fit != dt.finite_faces_end(); fit++)
    {

      // for(int k=0;k<=2;k++)
       {

               if(fit->info()[0]==1 )
               {
                   Edge e;
                   e.source = fit->vertex(2)->point();
                   e.target = fit->vertex(1)->point();
                   marked.push_back(e);
               }
               if(fit->info()[1]==1 )
               {
                   Edge e;
                   e.source = fit->vertex(2)->point();
                   e.target = fit->vertex(0)->point();
                   marked.push_back(e);
               }
               if(fit->info()[2]==1 )
               {
                   Edge e;
                   e.source = fit->vertex(0)->point();
                   e.target = fit->vertex(1)->point();
                   marked.push_back(e);
               }


       }

     }
}
void marked_edges1(void)
{
        int indx1 =0;
        for (Delaunay::Finite_vertices_iterator it = dt.finite_vertices_begin(); it != dt.finite_vertices_end(); it++)
        {
            indx1 =0;
            Delaunay::Vertex_circulator circulator = dt.incident_vertices(it), done(circulator);
            do
            {
                if(it->info()[indx1]==1 )
                {
                    Edge e;
                    e.source = it->point();
                    e.target = circulator->point();
                    marked.push_back(e);
                }
                indx1++;

            } while(++circulator != done);

        }
}
int main(int argc, char **argv)
{
    init();
    BOUNDARY_SAMPLE = 0;
    glutInit(&argc, argv);
    glutInitDisplayMode(GLUT_SINGLE | GLUT_RGBA);
    glutInitWindowSize(250, 250);
    wd = glutCreateWindow("Checking whethet the given point set is Boundary sample or not");
    repeat: std::ifstream ifs(argv[1]);
  //  std::cout<<" file name "<<argv[1]<<std::endl;
    if(ifs.fail())
    {
        printf("File does not exists\n");
        exit(1);
    }
    std::istream_iterator<Point> begin(ifs);
    std::istream_iterator<Point> end;
    dt.insert(begin, end);
    Delaunay::Vertex_iterator vi=dt.vertices_begin();
    ifs.close();
    do{
        if(vi->point().x()>maxx)
            maxx=vi->point().x();
        if(vi->point().y()>maxy)
            maxy=vi->point().y();
        if(vi->point().x()<minx)
            minx=vi->point().x();
        if(vi->point().y()<miny)
            miny=vi->point().y();
        input_points[vertex_count]=vi->point();
        vertex_count++;
        if(vertex_count>10000)
        {
            printf("Input size is too high, please increase the size of input_points and shape array\n");
            exit(1);
        }
        vi++;
    }while(vi!=dt.vertices_end());

    int flg =0;
    for (Delaunay::Finite_vertices_iterator it = dt.finite_vertices_begin(); it != dt.finite_vertices_end(); it++)
    {
        float dist[10000];
        int di=0;
        Delaunay::Vertex_circulator circulator = dt.incident_vertices(it), done(circulator);
        do
        {
            dist[di]=distance(circulator->point(),it->point());
            di++;
        } while(++circulator != done);
        float big=0,small=9999;
        for(int i=0;i<di;i++)
        {
            if(dist[i]>big)
            {
                big=dist[i];
            }
            if(dist[i]<small)
                small=dist[i];
        }
        if( (big<2*small) && di > 2) //if big < 2* small then it is a Dot pattern
             flg++;

    }


    float per = (float(flg)/float(vertex_count))*100;


    if(per == 0) // changed from 5 % to 0
    {
        BOUNDARY_SAMPLE = 1;
        std::cout<< "The input point set is Boundary sample. Pls use the any of the well known curve recon algo"<<std::endl;
        exit(0);
    }
    else
    {
        std::cout<< "The input point set is Dot Pattern or a boundary-sample which is not complying with the epsilon-sampling criteria."<<std::endl;
        std::cout<< "If the point set is boundary-sample and it is not complying with the epsilon-sampling criteria, "<<std::endl;
        std::cout<< "then the algorithm treat the point set as dot-patter which will return wrong result/no result"<<std::endl;
      }

    std::cout<<"Do you want to reconstruct?: (Press Y for yes) "<<std::endl;
    char contnue;
    std::cin>>contnue;

    if(contnue!='Y')
      exit(0);

    std::cout<<"Enter vertex size for displaying: "<<std::endl;
    std::cin>>vertex_size;

    choice=2;
      init_edges_status();

        if(!BOUNDARY_SAMPLE)
         {
            reconstruct();
            mark_outlier_edges();//mark_outlier_edges();
            retain_partiallymarked_shape_edges();
            retain_fullymarked_shape_edges();
            retain_partiallymarked_shape_edges();
            collect_shape_edges();
            collect_boundary_edges();
            if(choice == 2)
                remove_cycle();


       }
       else
        {
            std::cout<< "The input point set is Boundary sample; Pls use the any of the well known curve recon algo"<<std::endl;
            exit(0);
        }


    glutReshapeFunc(reshape);
    glutKeyboardFunc(kbd);
    glutDisplayFunc(display);
    glClearColor(1.0, 1.0, 1.0, 0.0);
    glColor3f(0.0, 0.0, 0.0);
    glLineWidth(3.0);
    glutMainLoop();
    exit(0);
    return 0;
}

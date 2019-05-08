
#include <stdio.h>
#include <stdlib.h>

#include <math.h>

/* Leaf optimization 'global' variables               */

static double P=1.0;
static double Q=1.0;

int main(int argc, char** argv);
double find_gradient_f (double pi_R, double pi_I, double* gradient);

int main(int argc, char** argv) {
    double val;
    double pi_R = 5.0;
    double pi_I = 2.5;
    double* gradient = malloc(2 * sizeof(double));
    gradient[0] = 3.2;
    gradient[1] = 1.1;

    val = find_gradient_f (pi_R, pi_I, gradient);
    
    printf("%f\n", val);
    
    return 0;
}

double find_gradient_f (double pi_R, double pi_I, double* gradient) {
    int i;
    double magnitude = 0.0;

    gradient[0]=1/(1+P)-pi_R;
    gradient[1]=1/(1+Q)-pi_I;
    
    for (i=0; i<2; i++)
      magnitude+=gradient[i]*gradient[i];
    
    //magnitude=sqrt (magnitude);
    
    for (i=0; i<2; i++)
      gradient[i]/=magnitude;

    return magnitude;
}


#include <stdio_checked.h>
#include <stdlib_checked.h>
#include <stdchecked.h>

#include <math.h>

#pragma CHECKED_SCOPE ON

/* Leaf optimization 'global' variables               */

static double P=1.0;
static double Q=1.0;

int main(int argc, _Array_ptr<_Nt_array_ptr<char>> argv : count(argc));
double find_gradient_f (double pi_R, double pi_I, _Array_ptr<double> gradient : count(2));

int main(int argc, _Array_ptr<_Nt_array_ptr<char>> argv : count(argc)) {
    double val;
    double pi_R = 5.0;
    double pi_I = 2.5;
    _Array_ptr<double> gradient : count(2) = malloc<double>(2 * sizeof(double));
    gradient[0] = 3.2;
    gradient[1] = 1.1;

    val = find_gradient_f (pi_R, pi_I, gradient);
    unchecked {
      printf("%f\n", val);
    }
    return 0;
}

double find_gradient_f (double pi_R, double pi_I, _Array_ptr<double> gradient : count(2)) {
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

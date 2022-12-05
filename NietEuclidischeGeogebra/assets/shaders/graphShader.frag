#version 400 core

in vec4 gl_FragCoord ;
layout(location = 0) out vec4 colour;

uniform vec4 u_Colour;

bool feq(float f1, float f2) {
	float epsilon = 0.1;
	if (abs(f1 - f2) <= epsilon)
		return true;
	return abs(f1 - f2) <= epsilon * max(abs(f1), abs(f2));
}

void main()
{
	colour = vec4(0.0, 0.0, 0.0, 1.0);

	vec2 xy = vec2((gl_FragCoord.x-550.)/200., (gl_FragCoord.y-225.)/200.);

	if (((((feq(1.000000, 1.000000) && feq(2.000000, 3.000000)) || (feq(2.000000, 1.000000) && feq(1.000000, 3.000000))) && feq(xy.y, 2.000000 * xy.x + 0.500000)) || (((feq(1.000000, 2.000000) && feq(2.000000, 3.000000)) || (feq(2.000000, 2.000000) && feq(1.000000, 3.000000))) && feq(xy.y, -2.000000 * xy.x + 0.500000)) || (((feq(1.000000, 1.000000) && feq(2.000000, 2.000000)) || (feq(2.000000, 1.000000) && feq(1.000000, 2.000000))) && feq(xy.y, -0.500000))) && (xy.x >= -0.500000 && xy.x <= 0.500000) && (xy.y >= -0.500000 && xy.y <= 0.500000)) {
		colour = u_Colour;
	}
}
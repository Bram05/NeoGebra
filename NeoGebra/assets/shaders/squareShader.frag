#version 400 core

layout(location = 0) out vec4 colour;

uniform vec4 u_Colour;
uniform vec2 u_Middle;
uniform vec2 u_Params;
in vec2 v_Pos;

void main()
{
	float x = v_Pos.x - u_Middle.x;
	float y = v_Pos.y - u_Middle.y;

	// GLSL's pow function is only defined for base > 0, but since the exponent is always even it is fine to just take the
	// absolute value of the base here
	if (u_Params.x * pow(abs(x),10) + u_Params.y * pow(abs(y),10) <= 1)
		colour = u_Colour;
	else
		colour = vec4(0.0, 0.0, 0.0, 0.0);
}

#version 400 core

layout(location = 0) out vec4 colour;

uniform vec4 u_Colour;
uniform vec2 u_Middle;
uniform vec2 u_Params;
in vec2 v_Pos;

void main()
{
	float x = v_Pos.x - u_Middle.x;
	float x4 = x * x * x * x * x * x * x * x * x * x;
	float y = v_Pos.y - u_Middle.y;
	float y4 = y * y * y * y * y * y * y * y * y * y;
	// colour = vec4(u_Params.x * x4 + u_Params.y * y4, 0.0, 0.0, 1.0);
	if (u_Params.x * x4 + u_Params.y * y4 <= 1)
		colour = u_Colour;
	else
		colour = vec4(0.0, 0.0, 0.0, 0.0);
}

#version 400

layout(location = 0) in vec2 pos;
out vec4 o_Pos;

void main()
{
	o_Pos = vec4(pos, 0.0, 0.0);
}